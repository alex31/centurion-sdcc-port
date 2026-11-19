/* Centurion CPU6 code generator. SPDX-License-Identifier: GPL-2.0-or-later */
#include "common.h"
#include "dbuf_string.h"
#include "peep.h"
#include <stdarg.h>
#include <stdint.h>
extern int cpu6_float32;

/* A/B are arithmetic scratch registers. X/Y/Z hold nonoverlapping live
   ranges and are preserved across calls. JSR/RSR save and restore caller X;
   Y/Z are saved explicitly when allocated. */
typedef struct {
  symbol *sym;
  unsigned size;
  int offset;
  int first, last;
  char reg;
  bool transient;
  bool parameter;
  unsigned weight;
  bitVect *live;
  symbol *address_base;
  uint16_t address_offset;
} cpu6_slot;

typedef struct {
  iCode *push;
  symbol *parameter;
  unsigned size, offset;
  bool direct;
} cpu6_tail_arg;
typedef struct cpu6_tail_site {
  iCode *call;
  cpu6_tail_arg *args;
  unsigned count, stack_bytes;
  struct cpu6_tail_site *next;
} cpu6_tail_site;

int cpu6_stack_only;
int cpu6_no_tail_recursion;
int cpu6_no_wide_native;
int cpu6_bitint48;
int cpu6_no_divmod;
int cpu6_no_wide_shifts;
int cpu6_simple_allocation;
int cpu6_no_frame_base;
int cpu6_no_tail_calls;
int cpu6_keep_static_functions;
int cpu6_no_inline48;
int cpu6_no_inplace_wide;
int cpu6_no_rhs_forwarding;
typedef struct cpu6_function_text {
  symbol *sym;
  char *text;
  struct cpu6_function_text *next;
} cpu6_function_text;
static cpu6_function_text *function_texts, **function_text_tail = &function_texts;
static bool inline_assembly_seen;
typedef struct cpu6_div_pair {
  iCode *first, *second;
  unsigned size, offset;
  struct cpu6_div_pair *next;
} cpu6_div_pair;
static cpu6_div_pair *div_pairs;
static unsigned div_bytes;
static unsigned private_base;
static unsigned register_scratch;
static operand *send_values[2];
static bool send_staged[2];
static iCode *receives[2];
static sym_link *called_type (iCode *ic)
{
  sym_link *type = operandType (ic->left);
  return IS_PTR (type) ? type->next : type;
}
static bool register_call (iCode *ic)
{
  sym_link *type = called_type (ic);
  if (!IS_FUNC (type) || IFFUNC_HASVARARGS (type)) return false;
  for (value *arg = FUNC_ARGS (type); arg; arg = arg->next)
    if (IS_REGPARM (arg->etype)) return true;
  return false;
}
extern int cpu6_no_byte_arithmetic;
static cpu6_slot *slots;
static unsigned nslots, capacity;
static int frame, saved, pushed;
static bool frame_base;
static unsigned frame_center;
static bool use_x, use_y, use_z, memory_saves_x;
static bool local_address_taken;
static unsigned local_label = 1000000;
static iCode *current_ic;
static iCode *function_chain;
static unsigned tail_body_label;
static cpu6_tail_site *tail_sites;
static symbol *b_cached;
static unsigned b_cached_width;
static bool asm_template;
static bool consumed_next (operand *op);

static void emit (const char *format, ...)
{
  struct dbuf_s buffer;
  dbuf_init (&buffer, 128);
  va_list args;
  va_start (args, format);
  dbuf_vprintf (&buffer, format, args);
  va_end (args);
  char *text = dbuf_detach_c_str (&buffer), *start = text;
  while (*start) {
    /* SDCC's preprocessor encodes newlines in the legacy __asm block. */
    char *end = asm_template ? strpbrk (start, "\n\x87") : strchr (start, '\n');
    if (end) *end = 0;
    while (isspace ((unsigned char)*start)) start++;
    if (*start) {
      initGenLineElement ();
      genLine.lineElement.ic = current_ic;
      genLine.lineElement.isLabel = start[strlen (start) - 1] == ':' && *start != ';';
      genLine.lineElement.isInline = asm_template;
      if (current_ic)
        genLine.lineElement.mightBeVolatileAccess =
          isOperandVolatile (current_ic->left, POINTER_GET (current_ic)) ||
          isOperandVolatile (current_ic->right, false) ||
          isOperandVolatile (current_ic->result, POINTER_SET (current_ic));
      emit_raw (start);
    }
    if (!end) break;
    start = end + 1;
  }
  dbuf_free (text);
}

static void unsupported (const char *what)
{
  fprintf (stderr, "cpu6: unsupported %s at %s:%d\n", what,
    current_ic && current_ic->filename ? current_ic->filename : "<input>",
    current_ic ? current_ic->lineno : 0);
  if (current_ic) {
    const char *line = printILine (current_ic);
    fprintf (stderr, "%s\n", line);
    dbuf_free (line);
  }
  exit (1);
}

static unsigned width (operand *op)
{
  if (!op) return 0;
  sym_link *type = operandType (op);
  if (IS_ARRAY (type) || IS_FUNC (type)) return 2;
  /* Constant propagation can encode an integer constant above INT32_MAX
     as a floating literal. Its integer consumer still requests conversion. */
  if ((IS_FLOAT (type) && !IS_VALOP (op) && !cpu6_float32) || IS_FIXED16X16 (type))
    unsupported ("floating point (enable --cpu6-float32 for float only)");
  unsigned size = getSize (type);
  if (size > 4 && IS_VALOP (op) && !(size == 6 && cpu6_bitint48 && IS_BITINT (type))) {
    double value = operandLitValue (op);
    /* SDCC also uses long-long literals for constant structure offsets. */
    if (current_ic && current_ic->result && IS_PTR (operandType (current_ic->result)) &&
        (current_ic->op == '+' || current_ic->op == '-') &&
        value >= -32768 && value <= 65535)
      size = 2;
    else if (value >= -2147483648.0 && value <= 4294967295.0)
      size = 4;
  }
  if (size == 6 && cpu6_bitint48 && IS_BITINT (type) && SPEC_BITINTWIDTH (getSpec (type)) == 48)
    return 6;
  if (IS_BITINT (type) && SPEC_BITINTWIDTH (getSpec (type)) != size * 8)
    unsupported ("non-byte-aligned _BitInt width");
  if (size > 4) unsupported ("scalar wider than 32 bits (use --cpu6-bitint48 for _BitInt(48))");
  if (size && size != 1 && size != 2 && size != 4)
    unsupported ("integer width other than 8, 16 or 32 bits");
  return size;
}

static bool unsigned_op (operand *op)
{
  sym_link *type = operandType (op);
  return IS_PTR (type) || IS_ARRAY (type) || IS_UNSIGNED (type) || IS_BOOL (type);
}

static cpu6_slot *slot_for (symbol *sym)
{
  for (unsigned i = 0; i < nslots; i++)
    if (slots[i].sym == sym) return slots + i;
  return NULL;
}

static void note_temp (operand *op, int seq)
{
  if (!IS_SYMOP (op) || IS_FUNC (operandType (op))) return;
  symbol *sym = OP_SYMBOL (op);
  bool parameter = !cpu6_stack_only && !IS_ITEMP (op) && sym->ismyparm &&
    sym->onStack && !sym->addrtaken && !isOperandVolatile (op, false) &&
    !IS_AGGREGATE (operandType (op)) && getSize (operandType (op)) <= 2;
  if (!IS_ITEMP (op) && !parameter) return;
  unsigned size = width (op);
  if (!size) return;
  cpu6_slot *slot = slot_for (sym);
  if (!slot) {
    if (nslots == capacity) {
      capacity = capacity ? capacity * 2 : 64;
      slots = realloc (slots, capacity * sizeof (*slots));
      wassert (slots);
    }
    slot = slots + nslots++;
    *slot = (cpu6_slot){.sym = sym, .size = size, .offset = -1,
                       .first = seq, .last = seq, .parameter = parameter};
  }
  if (sym->liveFrom && sym->liveFrom < slot->first) slot->first = sym->liveFrom;
  if (sym->liveTo > slot->last) slot->last = sym->liveTo;
  if (seq < slot->first) slot->first = seq;
  if (seq > slot->last) slot->last = seq;
  slot->weight += 1U << (current_ic->depth < 0 ? 0 : current_ic->depth > 4 ? 4 : current_ic->depth);
  if (op == current_ic->result && !POINTER_SET (current_ic) && consumed_next (op))
    slot->transient = true;
}

static bool overlap (cpu6_slot *a, cpu6_slot *b)
{
  if (a->first > b->last || b->first > a->last) return false;
  if (!cpu6_simple_allocation && !tail_sites && a->live && b->live)
    return bitVectBitsInCommon (a->live, b->live);
  return true;
}

static int by_weight (const void *left, const void *right)
{
  const cpu6_slot *a = left, *b = right;
  if (a->weight != b->weight) return a->weight < b->weight ? 1 : -1;
  return a->first < b->first ? -1 : a->first > b->first;
}

/* A linker-resolved address is cheaper to reload as an immediate than to
   spill and reload. Only single-definition pointer temporaries qualify. */
static void find_constant_addresses (iCode *chain)
{
  for (iCode *ic = chain; ic; ic = ic->next) {
    if (!IS_ITEMP (ic->result) || !IS_PTR (operandType (ic->result)) ||
        OP_SYMBOL (ic->result)->addrtaken || bitVectnBitsOn (OP_DEFS (ic->result)) != 1)
      continue;
    cpu6_slot *slot = slot_for (OP_SYMBOL (ic->result));
    if (ic->op == ADDRESS_OF && IS_TRUE_SYMOP (ic->left) && !OP_SYMBOL (ic->left)->onStack &&
        (!ic->right || IS_VALOP (ic->right))) {
      slot->address_base = OP_SYMBOL (ic->left);
      slot->address_offset = ic->right ? (uint16_t)(long long)operandLitValue (ic->right) : 0;
    } else if ((ic->op == CAST || ic->op == '=') && !POINTER_SET (ic) &&
               IS_ITEMP (ic->right) && IS_PTR (operandType (ic->right))) {
      cpu6_slot *base = slot_for (OP_SYMBOL (ic->right));
      if (base) {
        slot->address_base = base->address_base;
        slot->address_offset = base->address_offset;
      }
    } else if ((ic->op == '+' || ic->op == '-') && IS_ITEMP (ic->left) && IS_VALOP (ic->right)) {
      cpu6_slot *base = slot_for (OP_SYMBOL (ic->left));
      if (base && base->address_base) {
        uint16_t delta = (uint16_t)(long long)operandLitValue (ic->right);
        slot->address_base = base->address_base;
        slot->address_offset = base->address_offset + (ic->op == '+' ? delta : -delta);
      }
    }
  }
}

static void allocate (iCode *chain)
{
  for (unsigned i = 0; i < nslots; i++) if (slots[i].live) freeBitVect (slots[i].live);
  nslots = 0;
  use_x = use_y = use_z = false;
  local_address_taken = false;
  int seq = 0, temporary_bytes = 0, local_bytes = 0;
  for (iCode *ic = chain; ic; ic = ic->next) {
    current_ic = ic;
    if (ic->op == INLINEASM || (ic->op == ADDRESS_OF && IS_SYMOP (ic->left) && OP_SYMBOL (ic->left)->onStack))
      local_address_taken = true;
    seq++;
    /* SDCC sequence numbers include the ranges computed by its dataflow pass. */
    int pos = ic->seq ? ic->seq : seq;
    note_temp (ic->left, pos);
    note_temp (ic->right, pos);
    note_temp (ic->result, pos);
    operand *operands[] = {ic->left, ic->right, ic->result};
    for (unsigned n = 0; n < 3; n++)
      if (IS_TRUE_SYMOP (operands[n])) {
        symbol *sym = OP_SYMBOL (operands[n]);
        if (sym->onStack && (sym->addrtaken || IS_AGGREGATE (sym->type)))
          local_address_taken = true;
        if (sym->onStack && !sym->ismyparm && -sym->stack > local_bytes)
          local_bytes = -sym->stack;
      }
  }
  for (cpu6_tail_site *site = tail_sites; site; site = site->next)
    for (unsigned i = 0; i < site->count; i++) {
      operand *value = site->args[i].push->left;
      if (site->args[i].direct && IS_ITEMP (value)) {
        cpu6_slot *slot = slot_for (OP_SYMBOL (value));
        if (slot && slot->last < site->call->seq) slot->last = site->call->seq;
      }
    }
  for (unsigned i = 0; i < nslots; i++)
    if (slots[i].parameter) {
      slots[i].first = 0;
      slots[i].last = 0x7fffffff;
    }
  /* The shared dataflow pass records exact live points across the CFG. A
     single bounding interval needlessly conflicts across disjoint branches
     or separate definitions. Parameters remain conservative entry-to-exit. */
  if (!cpu6_simple_allocation && !tail_sites)
    for (unsigned i = 0; i < nslots; i++) {
      cpu6_slot *slot = slots + i;
      if (slot->parameter || slot->transient) continue;
      slot->live = newBitVect (seq + 1);
      unsigned point = 0;
      for (iCode *ic = chain; ic; ic = ic->next, point++) {
        bool present = bitVectBitValue (ic->rlive, slot->sym->key);
        operand *ops[] = {ic->left, ic->right, ic->result};
        for (unsigned n = 0; n < 3; n++)
          if (IS_SYMOP (ops[n]) && OP_SYMBOL (ops[n]) == slot->sym) present = true;
        if (present) slot->live = bitVectSetBit (slot->live, point);
      }
    }
  if (!cpu6_stack_only) {
    find_constant_addresses (chain);
    qsort (slots, nslots, sizeof (*slots), by_weight);
  }
  for (unsigned i = 0; i < nslots; i++) {
    cpu6_slot *slot = slots + i;
    if (slot->address_base) { slot->transient = false; continue; }
    if (slot->transient) continue;
    if (!cpu6_stack_only && slot->size <= 2 && !slot->sym->addrtaken &&
        (!slot->parameter || slot->weight >= 4)) {
      for (char reg = 'x'; reg <= (frame_base ? 'y' : 'z'); reg++) {
        bool free = true;
        for (unsigned j = 0; j < i; j++)
          if (slots[j].reg == reg && overlap (slot, slots + j)) free = false;
        if (free) {
          slot->reg = reg;
          if (reg == 'x') use_x = true;
          else if (reg == 'y') use_y = true;
          else use_z = true;
          break;
        }
      }
    }
    if (slot->reg || slot->parameter) continue;
    /* Reuse a slot only when every overlapping byte belongs to a disjoint
       live range. Local C objects occupy a separate part of the frame. */
    for (int offset = 0; ; offset++) {
      bool free = true;
      for (unsigned j = 0; j < i; j++) {
        cpu6_slot *other = slots + j;
        if (other->offset < 0 || !overlap (slot, other)) continue;
        if (offset < other->offset + (int)other->size &&
            other->offset < offset + (int)slot->size) free = false;
      }
      if (free) { slot->offset = offset; break; }
    }
    if (slot->offset + (int)slot->size > temporary_bytes)
      temporary_bytes = slot->offset + slot->size;
  }
  frame = local_bytes + temporary_bytes;
  /* Keep hot temporaries at the compact zero-displacement S address. Private
     results sit between temporaries and the addressable local objects. */
  private_base = temporary_bytes;
  frame += div_bytes + register_scratch;
  use_z |= frame_base;
  saved = 2 + 2 * use_y + 2 * use_z;
  pushed = 0;
  if (frame + saved > 32767) unsupported ("stack frame larger than 32767 bytes");
}

static int stack_offset (symbol *sym)
{
  cpu6_slot *slot = slot_for (sym);
  if (slot && !slot->parameter) return slot->offset + pushed;
  if (sym->ismyparm) {
    /* Byte parameters occupy the low byte of their big-endian ABI word. */
    return frame + saved + sym->stack + pushed + (getSize (sym->type) == 1);
  }
  return frame + sym->stack + pushed;
}

/* A fixed Z base covers a hot 256-byte window above the short S-relative
   range. Compare saved address construction against the cost of reserving Z
   and its prologue/epilogue. No ABI changes and no global scratch storage. */
static unsigned choose_frame_center (iCode *chain, bool force)
{
  if (cpu6_stack_only || cpu6_no_frame_base || frame < 128) return 0;
  unsigned *weights = calloc (32768, sizeof (*weights));
  wassert (weights);
  unsigned z_cost = 0;
  for (unsigned i = 0; i < nslots; i++) if (slots[i].reg == 'z') z_cost += slots[i].weight;
  for (iCode *ic = chain; ic; ic = ic->next) {
    if (ic->op == INLINEASM) { free (weights); return 0; }
    operand *ops[] = {ic->left, ic->right, ic->result};
    for (unsigned n = 0; n < 3; n++) {
      if (!IS_SYMOP (ops[n]) || IS_FUNC (operandType (ops[n]))) continue;
      symbol *sym = OP_SYMBOL (ops[n]);
      cpu6_slot *slot = slot_for (sym);
      if ((!sym->onStack && !slot) || (slot && (slot->reg || slot->transient || slot->address_base))) continue;
      unsigned size = getSize (operandType (ops[n]));
      if (size > 6) size = 2; /* aggregate address, not a full scalar load */
      for (unsigned offset = 0; offset < size; offset += 2) {
        int pos = stack_offset (sym) + offset;
        if (pos > 127 && pos < 32768)
          weights[pos] += 1U << (ic->depth < 0 ? 0 : ic->depth > 4 ? 4 : ic->depth);
      }
    }
  }
  unsigned sum = 0, best = 0, center = 128;
  for (unsigned pos = 0; pos < 32768; pos++) {
    sum += weights[pos];
    if (pos >= 256) sum -= weights[pos - 256];
    if (sum > best) { best = sum; center = pos >= 255 ? pos - 127 : 128; }
  }
  free (weights);
  return force || best * 64 > z_cost * 24 + 150 ? center : 0;
}

static const char *symbol_name (symbol *sym)
{
  if (strlen (sym->rname) > 16 && (IS_STATIC (sym->etype) || sym->isstrlit)) {
    /* Stable within a compilation; local symbols do not cross object files. */
    unsigned hash = 2166136261U;
    for (const char *p = sym->rname; *p; p++) hash = (hash ^ (unsigned char)*p) * 16777619U;
    snprintf (sym->rname, sizeof (sym->rname), "__c6_%08x", hash);
  }
  else if (strlen (sym->rname) > 32)
    unsupported ("external symbol longer than the CPU6 port's spelling limit");
  return sym->rname;
}

const char *cpu6SymbolName (symbol *sym)
{
  return symbol_name (sym);
}

static bool stacked (symbol *sym)
{
  return sym->onStack || slot_for (sym);
}

static bool register_needed (char reg)
{
  if (cpu6_simple_allocation || !current_ic || current_ic->op == FUNCTION) return reg == 'x' && use_x;
  for (unsigned i = 0; i < nslots; i++) {
    cpu6_slot *slot = slots + i;
    if (slot->reg != reg) continue;
    if (slot->parameter) return true;
    operand *ops[] = {current_ic->left, current_ic->right,
                     POINTER_SET (current_ic) ? current_ic->result : NULL};
    for (unsigned n = 0; n < 3; n++)
      if (IS_SYMOP (ops[n]) && OP_SYMBOL (ops[n]) == slot->sym) return true;
    for (unsigned n = 0; n < 2; n++)
      if (IS_SYMOP (send_values[n]) && OP_SYMBOL (send_values[n]) == slot->sym) return true;
    if (bitVectBitValue (current_ic->rlive, slot->sym->key) &&
        !(IS_SYMOP (current_ic->result) && !POINTER_SET (current_ic) && OP_SYMBOL (current_ic->result) == slot->sym))
      return true;
    if (tail_sites && slot->first < current_ic->seq && slot->last >= current_ic->seq) return true;
  }
  return false;
}

/* Compute addresses using X only, leaving both arithmetic operands intact. */
static void memory_operand (symbol *sym, int offset, char *text, size_t length)
{
  memory_saves_x = false;
  cpu6_slot *slot = slot_for (sym);
  if (slot && slot->address_base) {
    wassert (!offset);
    snprintf (text, length, "%s+%u", symbol_name (slot->address_base), (unsigned)slot->address_offset);
  } else if (stacked (sym)) {
    int pos = stack_offset (sym) + offset;
    if (pos >= -128 && pos <= 127) snprintf (text, length, "%d(s)", pos);
    else if (frame_base && pos - pushed - (int)frame_center >= -128 && pos - pushed - (int)frame_center <= 127)
      snprintf (text, length, "%d(z)", pos - pushed - (int)frame_center);
    else {
      if (register_needed ('x')) {
        emit ("\tstx (-s)\n");
        pushed += 2; pos += 2;
        memory_saves_x = true;
      }
      emit ("\tldx %u\n\tadd s,x\n", (unsigned)pos & 65535);
      snprintf (text, length, "(x)");
    }
  } else snprintf (text, length, "(%s+%d)", symbol_name (sym), offset);
}

static void memory_done (void)
{
  if (memory_saves_x) {
    emit ("\tldx (s+)\n");
    pushed -= 2;
    memory_saves_x = false;
  }
}

static void address (symbol *sym, int offset)
{
  if (stacked (sym))
    emit ("\tldb %u\n\tadd s,b\n", (unsigned)(stack_offset (sym) + offset) & 65535);
  else emit ("\tldb %s+%d\n", symbol_name (sym), offset);
}

static void extend_byte (bool unsign)
{
  emit ("\tclrb bh\n");
  if (!unsign) {
    unsigned label = local_label++;
    emit ("\torib bl,bl\n\tbp L%u\n\tdcrb bh\nL%u:\n", label, label);
  }
}

static void extend_long (bool unsign)
{
  emit ("\tcla\n");
  if (!unsign) {
    unsigned label = local_label++;
    emit ("\tori b,b\n\tbp L%u\n\tdca\nL%u:\n", label, label);
  }
  emit ("\tsta (__hireg)\n");
}

static void load (operand *op, unsigned wanted)
{
  if (!op) unsupported ("missing operand");
  unsigned size = width (op);
  if (wanted == 6 && size < 6) {
    load (op, 4);
    emit ("\tlda (__hireg)\n\tsta (__cpu6_mid48)\n");
    if (unsigned_op (op)) emit ("\tcla\n");
    else {
      unsigned positive = local_label++, done = local_label++;
      emit ("\tori a,a\n\tbp L%u\n\tlda 65535\n\tbra L%u\nL%u:\n\tcla\nL%u:\n",
            positive, done, positive, done);
    }
    emit ("\tsta (__hireg)\n"); b_cached = NULL;
    return;
  }
  if (size == 6) {
    if (IS_SYMOP (op) && b_cached == OP_SYMBOL (op) && b_cached_width == 6) {
      if (wanted == 6) return;
      if (wanted == 4) emit ("\tlda (__cpu6_mid48)\n\tsta (__hireg)\n");
      b_cached = NULL;
      return;
    }
    b_cached = NULL;
    if (IS_VALOP (op)) {
      unsigned long long value = (unsigned long long)(long long)operandLitValue (op);
      if (wanted == 6) emit ("\tlda %u\n\tsta (__hireg)\n\tlda %u\n\tsta (__cpu6_mid48)\n",
                            (unsigned)(value >> 32) & 65535, (unsigned)(value >> 16) & 65535);
      else if (wanted == 4) emit ("\tlda %u\n\tsta (__hireg)\n", (unsigned)(value >> 16) & 65535);
      emit ("\tldb %u\n", (unsigned)value & 65535);
    } else {
      char mem[400]; symbol *sym = OP_SYMBOL (op);
      if (wanted == 6) {
        memory_operand (sym, 0, mem, sizeof (mem));
        emit ("\tlda %s\n\tsta (__hireg)\n", mem); memory_done ();
      }
      if (wanted >= 4) {
        memory_operand (sym, 2, mem, sizeof (mem));
        emit ("\tlda %s\n\tsta (%s)\n", mem, wanted == 6 ? "__cpu6_mid48" : "__hireg"); memory_done ();
      }
      memory_operand (sym, 4, mem, sizeof (mem));
      emit ("\tldb %s\n", mem); memory_done ();
      if (wanted == 6 && IS_ITEMP (op) && !sym->addrtaken) {
        b_cached = sym; b_cached_width = 6;
      }
    }
    return;
  }
  if (IS_VALOP (op)) {
    b_cached = NULL;
    if (cpu6_float32 && IS_FLOAT (operandType (op))) {
      union {float f; uint32_t u;} bits;
      bits.f = (float)operandLitValue (op);
      if (wanted != 4) unsupported ("unlowered floating conversion");
      emit ("\tlda %u\n\tsta (__hireg)\n\tldb %u\n", (unsigned)(bits.u >> 16), (unsigned)(bits.u & 65535));
      return;
    }
    unsigned long value = (unsigned long)(long long)operandLitValue (op);
    if (wanted == 4) emit ("\tlda %u\n\tsta (__hireg)\n", (unsigned)(value >> 16) & 65535);
    emit ("\tldb %u\n", (unsigned)value & (size == 1 ? 255 : 65535));
    if (size == 1) extend_byte (unsigned_op (op));
    if (wanted == 4 && size < 4) extend_long (unsigned_op (op));
    return;
  }
  if (!IS_SYMOP (op)) unsupported ("non-value operand");
  symbol *sym = OP_SYMBOL (op);
  sym_link *type = operandType (op);
  if (IS_ARRAY (type) || IS_FUNC (type)) {
    b_cached = NULL;
    address (sym, 0);
    if (wanted == 4) extend_long (true);
    return;
  }
  cpu6_slot *slot = slot_for (sym);
  unsigned needed = size < wanted ? size : wanted;
  bool cached = !cpu6_stack_only && b_cached == sym && b_cached_width >= needed;
  if (slot && slot->transient && !cached) unsupported ("lost transient B value");
  if (!cached && slot && slot->reg) emit ("\txfr %c,b\n", slot->reg);
  else if (!cached) {
    char mem[400];
    if (size == 4 && wanted == 4) {
      memory_operand (sym, 0, mem, sizeof (mem));
      emit ("\tldb %s\n\tstb (__hireg)\n", mem);
      memory_done ();
    }
    memory_operand (sym, size == 4 ? 2 : 0, mem, sizeof (mem));
    emit (size == 1 ? "\tldbb %s\n" : "\tldb %s\n", mem);
    memory_done ();
  }
  if (size == 1) extend_byte (unsigned_op (op));
  if (wanted == 4 && size < 4) extend_long (unsigned_op (op));
  b_cached = (IS_ITEMP (op) || (slot && slot->parameter && slot->reg)) && !sym->addrtaken ? sym : NULL;
  b_cached_width = needed;
}

/* Read an existing word register without first routing it through B. */
static char word_register (operand *op)
{
  if (!IS_SYMOP (op) || width (op) != 2 || IS_ARRAY (operandType (op)) ||
      IS_FUNC (operandType (op))) return 0;
  cpu6_slot *slot = slot_for (OP_SYMBOL (op));
  return slot ? slot->reg : 0;
}

/* Word arithmetic can read the left operand directly into A. All address
   formation here uses X, so a cached value in B remains available. */
static void load_word_a (operand *op)
{
  unsigned size = width (op);
  if (IS_VALOP (op) && size == 2) {
    emit ("\tlda %u\n", (unsigned)(long long)operandLitValue (op) & 65535);
    return;
  }
  if (IS_SYMOP (op) && size == 2 && !IS_ARRAY (operandType (op)) && !IS_FUNC (operandType (op))) {
    symbol *sym = OP_SYMBOL (op);
    cpu6_slot *slot = slot_for (sym);
    if (!cpu6_stack_only && b_cached == sym && b_cached_width >= 2)
      emit ("\txfr b,a\n");
    else if (slot && slot->reg) emit ("\txfr %c,a\n", slot->reg);
    else if (slot && slot->transient) unsupported ("lost transient A source");
    else {
      char mem[400];
      memory_operand (sym, 0, mem, sizeof (mem));
      emit ("\tlda %s\n", mem);
      memory_done ();
    }
    return;
  }
  load (op, 2);
  emit ("\txfr b,a\n");
}

/* Read only the low byte needed by a truncated arithmetic result. Volatile
   word objects must still be read with their original word access width. */
static void load_low_byte (operand *op, char reg)
{
  unsigned size = width (op);
  wassert (size == 1 || size == 2);
  if (IS_VALOP (op)) {
    emit ("\tld%cb %u\n", reg, (unsigned)(long long)operandLitValue (op) & 255);
    if (reg == 'b') b_cached = NULL;
    return;
  }
  if (!IS_SYMOP (op)) unsupported ("non-value byte operand");
  symbol *sym = OP_SYMBOL (op);
  cpu6_slot *slot = slot_for (sym);
  bool cached = !cpu6_stack_only && b_cached == sym && b_cached_width >= 1;
  if (slot && slot->transient && !cached) unsupported ("lost transient byte value");
  if (cached) {
    if (reg != 'b') emit ("\txfrb bl,%cl\n", reg);
  } else if (slot && slot->reg) emit ("\txfrb %cl,%cl\n", slot->reg, reg);
  else {
    bool full = size == 2 && (isOperandVolatile (op, false) || (slot && slot->address_base));
    char mem[400];
    memory_operand (sym, full ? 0 : size - 1, mem, sizeof (mem));
    if (full) emit ("\tld%c %s\n", reg, mem);
    else emit ("\tld%cb %s\n", reg, mem);
    memory_done ();
  }
  if (reg == 'b') {
    b_cached = (IS_ITEMP (op) || (slot && slot->parameter && slot->reg)) && !sym->addrtaken ? sym : NULL;
    b_cached_width = 1;
  }
}

static bool split_long_operand (operand *op)
{
  return IS_VALOP (op) || (IS_SYMOP (op) && width (op) == 4 && !isOperandVolatile (op, false));
}

static void load_scalar_part (operand *op, unsigned offset, char reg, unsigned bytes)
{
  if (IS_VALOP (op)) {
    unsigned long long value = (unsigned long long)(long long)operandLitValue (op);
    emit ("\tld%c %u\n", reg, (unsigned)(value >> ((bytes - offset - 2) * 8)) & 65535);
  } else {
    char mem[400];
    memory_operand (OP_SYMBOL (op), offset, mem, sizeof (mem));
    emit ("\tld%c %s\n", reg, mem);
    memory_done ();
  }
}

static void load_long_part (operand *op, unsigned offset, char reg)
{
  load_scalar_part (op, offset, reg, 4);
}

/* A single-use temporary consumed first by the next instruction can remain
   in B. Other temporaries still have a physical home for later reloads. */
static bool consumed_next (operand *op)
{
  if (current_ic->op == RECEIVE) return false;
  if (cpu6_stack_only || !IS_ITEMP (op) || OP_SYMBOL (op)->addrtaken ||
      bitVectnBitsOn (OP_USES (op)) != 1 || bitVectnBitsOn (OP_DEFS (op)) != 1)
    return false;
  iCode *next = current_ic->next;
  if (!next || next->generated || next->op == SEND) return false;
  /* A word consumer reads its left scalar directly into A, preserving the
     right operand already in B. Giving this single-use value a stack/register
     home only creates a dead spill and increases interference. This is not
     valid for byte extension, aggregate addresses, variable shifts (which
     push the left operand through B), or split-word lowering. */
  if (!cpu6_no_rhs_forwarding && width (op) == 2 &&
      IS_SYMOP (next->right) && OP_SYMBOL (next->right) == OP_SYMBOL (op) &&
      next->left && width (next->left) == 2 &&
      !IS_ARRAY (operandType (next->left)) && !IS_FUNC (operandType (next->left))) {
    switch (next->op) {
      case '+': case '-': case '*': case '/': case '%': case BITWISEAND: case '|': case '^':
        if (width (next->result) == 2) return true;
        break;
      case EQ_OP: case NE_OP: case '<': case '>': case LE_OP: case GE_OP:
        return true;
    }
  }
  if (width (op) == 6)
    switch (next->op) {
      case EQ_OP: case NE_OP: case '<': case '>': case LE_OP: case GE_OP:
        return false;
    }
  /* Split-word lowering revisits the high half after B has been reused.
     Such inputs need a real home, rather than a transient slot at offset -1. */
  if (width (op) == 4 && !cpu6_no_wide_native && !optimize.codeSize)
    switch (next->op) {
      case '+': case '-': case BITWISEAND: case '|': case '^':
      case EQ_OP: case NE_OP: case '<': case '>': case LE_OP: case GE_OP:
        return false;
    }
  operand *first = NULL;
  if (POINTER_SET (next)) first = next->result;
  else switch (next->op) {
    case '=': case CAST: first = next->right; break;
    case '+': case '-': case '*': case '/': case '%': case BITWISEAND:
    case '|': case '^': case LEFT_OP: case RIGHT_OP: case UNARYMINUS:
    case '!': case '~': case IFX: case RETURN: case IPUSH:
    case EQ_OP: case NE_OP: case '<': case '>': case LE_OP: case GE_OP:
    case GET_VALUE_AT_ADDRESS: case JUMPTABLE:
      first = next->left; break;
  }
  return IS_SYMOP (first) && OP_SYMBOL (first) == OP_SYMBOL (op);
}

static void store (operand *op)
{
  if (!op || !width (op)) return;
  if (!IS_SYMOP (op)) unsupported ("non-symbol destination");
  symbol *sym = OP_SYMBOL (op);
  unsigned size = width (op);
  cpu6_slot *slot = slot_for (sym);
  b_cached = (IS_ITEMP (op) || (slot && slot->parameter && slot->reg)) && !sym->addrtaken ? sym : NULL;
  b_cached_width = size;
  if (consumed_next (op)) return;
  if (slot && slot->reg) {
    emit ("\txfr b,%c\n", slot->reg);
    return;
  }
  char mem[400];
  if (size == 6) {
    memory_operand (sym, 0, mem, sizeof (mem));
    emit ("\tlda (__hireg)\n\tsta %s\n", mem); memory_done ();
    memory_operand (sym, 2, mem, sizeof (mem));
    emit ("\tlda (__cpu6_mid48)\n\tsta %s\n", mem); memory_done ();
    memory_operand (sym, 4, mem, sizeof (mem));
    emit ("\tstb %s\n", mem); memory_done ();
    return;
  }
  if (size == 4) {
    memory_operand (sym, 0, mem, sizeof (mem));
    emit ("\tlda (__hireg)\n\tsta %s\n", mem);
    memory_done ();
  }
  memory_operand (sym, size == 4 ? 2 : 0, mem, sizeof (mem));
  emit (size == 1 ? "\tstbb %s\n" : "\tstb %s\n", mem);
  memory_done ();
}

static void push (operand *op, unsigned size)
{
  load (op, size);
  emit ("\tstb (-s)\n");
  pushed += 2;
  if (size == 6) {
    emit ("\tlda (__cpu6_mid48)\n\tsta (-s)\n"); pushed += 2;
  }
  if (size >= 4) {
    emit ("\tlda (__hireg)\n\tsta (-s)\n");
    pushed += 2;
  }
}

static void stack_address_arg (unsigned offset, int base)
{
  emit ("\tldb %u\n\tadd s,b\n\tstb (-s)\n", offset + pushed - base);
  pushed += 2;
}

static void reserve_stack (unsigned bytes)
{
  emit ("\tlda %u\n\tadd a,s\n", (65536 - bytes) & 65535);
  pushed += bytes;
}

static void add_sub48 (iCode *ic)
{
  bool add = ic->op == '+';
  const char *op = add ? "aab" : "sab";
  unsigned no_input = local_label++, carry = local_label++, mid_join = local_label++;
  unsigned no_high = local_label++, high_join = local_label++;
  push (ic->left, 6); push (ic->right, 6);
  emit ("\tlda 10(s)\n\tldb 4(s)\n\t%s\n\tstb 10(s)\n", op);
  emit (add ? "\tbnl L%u\n" : "\tbl L%u\n", no_input);
  emit ("\tlda 8(s)\n\tldb 2(s)\n\t%s\n", op);
  if (add) {
    unsigned wrapped = local_label++;
    emit ("\tbl L%u\n\tinr b\n\tbz L%u\n\trl\n\tbra L%u\nL%u:\n\tinr b\nL%u:\n\tsl\n",
          carry, wrapped, mid_join, carry, wrapped);
  } else {
    emit ("\tbnl L%u\n\tori b,b\n\tbz L%u\n\tdcr b\n\tsl\n\tbra L%u\nL%u:\n\tdcr b\n\trl\n",
          carry, carry, mid_join, carry);
  }
  emit ("\tbra L%u\nL%u:\n\tlda 8(s)\n\tldb 2(s)\n\t%s\nL%u:\n\tstb 8(s)\n",
        mid_join, no_input, op, mid_join);
  emit (add ? "\tbnl L%u\n" : "\tbl L%u\n", no_high);
  emit ("\tlda 6(s)\n\tldb 0(s)\n\t%s\n\t%s b\n\tbra L%u\nL%u:\n",
        op, add ? "inr" : "dcr", high_join, no_high);
  emit ("\tlda 6(s)\n\tldb 0(s)\n\t%s\nL%u:\n\tstb (__hireg)\n", op, high_join);
  emit ("\tlda 8(s)\n\tsta (__cpu6_mid48)\n\tldb 10(s)\n\tlda 12\n\tadd a,s\n");
  pushed -= 12; b_cached = NULL;
}

/* The pointer library and the native scalar have identical six-byte layouts.
   Operand snapshots preserve aliases, expression evaluation and nested calls. */
static void arithmetic48 (iCode *ic)
{
  bool shift = ic->op == LEFT_OP || ic->op == RIGHT_OP;
  bool unary = ic->op == UNARYMINUS;
  bool unsign = unsigned_op (ic->left);
  if (!cpu6_no_inline48 && !optimize.codeSize && (ic->op == '+' || ic->op == '-')) {
    add_sub48 (ic); return;
  }
  if (shift && IS_VALOP (ic->right) && operandLitValue (ic->right) == 1) {
    load (ic->left, 6);
    if (ic->op == LEFT_OP)
      emit ("\tslr b\n\tlda (__cpu6_mid48)\n\trlr a\n\tsta (__cpu6_mid48)\n"
            "\tlda (__hireg)\n\trlr a\n\tsta (__hireg)\n");
    else {
      emit ("\tlda (__hireg)\n");
      emit (unsign ? "\trl\n\trrr a\n" : "\tsrr a\n");
      emit ("\tsta (__hireg)\n\tlda (__cpu6_mid48)\n\trrr a\n\tsta (__cpu6_mid48)\n\trrr b\n");
    }
    b_cached = NULL;
    return;
  }
  int start = pushed;
  push (ic->left, 6);
  unsigned right_bytes = unary ? 0 : shift ? 2 : 6;
  if (!unary) push (ic->right, right_bytes);
  if (ic->op == BITWISEAND || ic->op == '|' || ic->op == '^') {
    const char *instruction = ic->op == BITWISEAND ? "nab" : ic->op == '|' ? "ori a,b" : "ore a,b";
    for (unsigned offset = 0; offset < 6; offset += 2) {
      emit ("\tlda %u(s)\n\tldb %u(s)\n\t%s\n", 6 + offset, offset, instruction);
      if (offset < 4) emit ("\tstb (%s)\n", offset ? "__cpu6_mid48" : "__hireg");
    }
  } else {
    reserve_stack (6);
    int base = pushed;
    const char *helper = NULL;
    if (ic->op == '/' || ic->op == '%') {
      stack_address_arg (6, base);  /* divisor */
      stack_address_arg (12, base); /* numerator */
      if (ic->op == '%') stack_address_arg (0, base);
      else { emit ("\tclr b\n\tstb (-s)\n"); pushed += 2; }
      if (ic->op == '/') stack_address_arg (0, base);
      else { emit ("\tclr b\n\tstb (-s)\n"); pushed += 2; }
      helper = unsign ? "_u48_divmod" : "_i48_divmod";
    } else {
      if (shift) { emit ("\tldb 6(s)\n\tstb (-s)\n"); pushed += 2; }
      else if (!unary) stack_address_arg (6, base);
      stack_address_arg (6 + right_bytes, base);
      stack_address_arg (0, base);
      switch (ic->op) {
        case '+': helper = "_u48_add"; break;
        case '-': helper = "_u48_sub"; break;
        case '*': helper = "_u48_mul"; break;
        case UNARYMINUS: helper = "_u48_neg"; break;
        case LEFT_OP: helper = "_u48_shl"; break;
        case RIGHT_OP: helper = unsign ? "_u48_shr" : "_i48_shr"; break;
        default: unsupported ("48-bit arithmetic operation");
      }
    }
    emit ("\tjsr %s\n", helper);
    unsigned offset = pushed - base;
    emit ("\tlda %u(s)\n\tsta (__hireg)\n\tlda %u(s)\n\tsta (__cpu6_mid48)\n\tldb %u(s)\n",
          offset, offset + 2, offset + 4);
  }
  emit ("\tlda %u\n\tadd a,s\n", pushed - start);
  pushed = start;
  b_cached = NULL;
}

static void boolify (unsigned size, bool inverse)
{
  if (size >= 4) emit ("\tlda (__hireg)\n\tori a,b\n");
  if (size == 6) emit ("\tlda (__cpu6_mid48)\n\tori a,b\n");
  emit (inverse ? "\tjsr __not\n" : "\tjsr __bool\n");
}

/* Float truth ignores the sign bit so both zeros are false. The integer
   magnitude test also makes every NaN true, as required by C conversion. */
static void float_truth (operand *op)
{
  load (op, 4);
  emit ("\tstx (-s)\n\tldx 32767\n\tlda (__hireg)\n\tand x,a\n\tori a,b\n\tldx (s+)\n");
  b_cached = NULL;
}

static const char *compare_name (unsigned op)
{
  switch (op) {
    case EQ_OP: return "eq";
    case NE_OP: return "ne";
    case '<': return "lt";
    case '>': return "gt";
    case LE_OP: return "lteq";
    case GE_OP: return "gteq";
  }
  unsupported ("comparison");
  return "";
}

static iCode *comparison_branch (iCode *ic)
{
  iCode *next = IS_ITEMP (ic->result) ? ifxForOp (ic->result, ic) : NULL;
  if (next && next->op == IFX && IS_ITEMP (ic->result) && IS_SYMOP (next->left) &&
      OP_SYMBOL (ic->result) == OP_SYMBOL (next->left) &&
      bitVectnBitsOn (OP_USES (ic->result)) == 1)
    return next;
  return NULL;
}

/* A byte promotion can survive as a word CAST after the generic value map
   has been discarded. Recover its source range only for a unique definition
   and a conversion that preserves that range. */
static struct valinfo word_info (iCode *ic, operand *op)
{
  struct valinfo v = getOperandValinfo (ic, op, false);
  if (IS_ITEMP (op) && IS_INTEGRAL (operandType (op)) && width (op) == 2 &&
      bitVectnBitsOn (OP_DEFS (op)) == 1) {
    iCode *def = hTabItemWithKey (iCodehTab, bitVectFirstBit (OP_DEFS (op)));
    if (def && def->op == CAST && IS_INTEGRAL (operandType (def->right)) && width (def->right) == 1 &&
        (unsigned_op (def->right) || !unsigned_op (op))) {
      struct valinfo byte = getOperandValinfo (def, def->right, false);
      if (!byte.anything && !byte.nothing && (v.anything || v.min < byte.min || v.max > byte.max))
        return byte;
    }
  }
  return v;
}

static void jump_condition (unsigned op, bool unsign, iCode *branch, bool no_overflow)
{
  symbol *target = IC_TRUE (branch) ? IC_TRUE (branch) : IC_FALSE (branch);
  if (!IC_TRUE (branch)) {
    switch (op) {
      case EQ_OP: op = NE_OP; break;
      case NE_OP: op = EQ_OP; break;
      case '<': op = GE_OP; break;
      case '>': op = LE_OP; break;
      case LE_OP: op = '>'; break;
      case GE_OP: op = '<'; break;
    }
  }
  unsigned skip = local_label++, take = local_label++, overflow = local_label++;
  if (op == EQ_OP) emit ("\tbnz L%u\n", skip);
  else if (op == NE_OP) emit ("\tbz L%u\n", skip);
  else if (unsign) {
    if (op == '>') emit ("\tbz L%u\n", skip);
    if (op == LE_OP) emit ("\tbz L%u\n", take);
    emit (op == '<' || op == LE_OP ? "\tbl L%u\n" : "\tbnl L%u\n", skip);
  } else {
    if (op == '>') emit ("\tbz L%u\n", skip);
    if (op == LE_OP) emit ("\tbz L%u\n", take);
    if (no_overflow)
      emit (op == '<' || op == LE_OP ? "\tbp L%u\n" : "\tbm L%u\n", skip);
    else {
      emit ("\tbf L%u\n", overflow);
      emit (op == '<' || op == LE_OP ? "\tbp L%u\n" : "\tbm L%u\n", skip);
      emit ("\tbra L%u\nL%u:\n", take, overflow);
      emit (op == '<' || op == LE_OP ? "\tbm L%u\n" : "\tbp L%u\n", skip);
    }
  }
  if (op == LE_OP || (!unsign && op != EQ_OP && op != NE_OP))
    emit ("L%u:\n", take);
  emit ("\tjmp L%d\nL%u:\n", target->key, skip);
  branch->generated = 1;
  b_cached = NULL;
}

static void compare (iCode *ic)
{
  unsigned size = width (ic->left);
  if (width (ic->right) > size) size = width (ic->right);
  bool unsign = unsigned_op (ic->left);
  const char *name = compare_name (ic->op);
  const char *suffix = (ic->op == EQ_OP || ic->op == NE_OP || !unsign) ? "" : "u";
  iCode *branch = comparison_branch (ic);
  if (size == 6) {
    unsigned truth = local_label++, done = local_label++;
    symbol target = {0}; target.key = truth;
    iCode test = {0}; test.op = IFX; IC_TRUE (&test) = &target;
    iCode *condition = branch ? branch : &test;
    bool direct = (IS_VALOP (ic->left) || (width (ic->left) == 6 && !isOperandVolatile (ic->left, false))) &&
                  (IS_VALOP (ic->right) || (width (ic->right) == 6 && !isOperandVolatile (ic->right, false)));
    if (direct) {
      for (unsigned offset = 0; offset < 6; offset += 2) {
        unsigned next = local_label++;
        load_scalar_part (ic->left, offset, 'a', 6);
        load_scalar_part (ic->right, offset, 'b', 6);
        emit ("\tsab\n");
        if (offset < 4) emit ("\tbz L%u\n", next);
        jump_condition (ic->op, offset ? true : unsign, condition, false);
        if (offset < 4) emit ("\tjmp L%u\nL%u:\n", done, next);
      }
    } else {
      int start = pushed;
      push (ic->left, 6); push (ic->right, 6);
      int base = pushed;
      stack_address_arg (0, base); stack_address_arg (6, base);
      emit ("\tjsr %s\n\tlda 16\n\tadd a,s\n\tori b,b\n", unsign ? "_u48_cmp" : "_i48_cmp");
      pushed = start;
      jump_condition (ic->op, false, condition, true);
    }
    emit ("L%u:\n", done);
    b_cached = NULL;
    if (!branch) {
      unsigned end = local_label++;
      emit ("\tclr b\n\tbra L%u\nL%u:\n\tldb 1\nL%u:\n", end, truth, end);
      store (ic->result);
    }
    return;
  }
  if (size == 4) {
    if (!cpu6_no_wide_native && !optimize.codeSize && branch &&
        split_long_operand (ic->left) && split_long_operand (ic->right)) {
      b_cached = NULL;
      unsigned low = local_label++, done = local_label++;
      load_long_part (ic->left, 0, 'a'); load_long_part (ic->right, 0, 'b');
      emit ("\tsab\n\tbz L%u\n", low);
      jump_condition (ic->op, unsign, branch, false);
      emit ("\tjmp L%u\nL%u:\n", done, low);
      load_long_part (ic->left, 2, 'a'); load_long_part (ic->right, 2, 'b');
      emit ("\tsab\n");
      /* Once high words are equal, low words are always unsigned. */
      jump_condition (ic->op, true, branch, false);
      emit ("L%u:\n", done);
      return;
    }
    push (ic->left, 4);
    load (ic->right, 4);
    emit ("\tjsr __cc%s%sl\n", name, suffix);
    pushed -= 4;
    if (branch) {
      emit ("\tori b,b\n");
      jump_condition (NE_OP, true, branch, false);
      return;
    }
  } else {
    if (branch && !unsign && IS_VALOP (ic->right) && operandLitValue (ic->right) == 0) {
      load (ic->left, 2);
      /* Test N/Z directly: subtracting zero cannot overflow, whereas an
         ordinary load intentionally preserves the old overflow flag. */
      emit ("\tori b,b\n");
      jump_condition (ic->op, false, branch, true);
      return;
    }
    if (IS_VALOP (ic->right)) {
      load (ic->left, 2);
      emit ("\tlda %u\n\tsub b,a\n", (unsigned)(long long)operandLitValue (ic->right) & 65535);
    } else {
      load_word_a (ic->left);
      load (ic->right, 2);
      emit ("\tsab\n");
    }
    if (branch) {
      bool no_overflow = false;
      if (!unsign && ic->op != EQ_OP && ic->op != NE_OP) {
        struct valinfo a = word_info (ic, ic->left);
        struct valinfo b = word_info (ic, ic->right);
        no_overflow = !a.anything && !a.nothing && !b.anything && !b.nothing &&
          a.min >= -32768 && a.max <= 32767 && b.min >= -32768 && b.max <= 32767 &&
          a.min - b.max >= -32768 && a.max - b.min <= 32767;
      }
      jump_condition (ic->op, unsign, branch, no_overflow);
      return;
    }
    emit ("\tjsr __cc%s%s\n", name, suffix);
  }
  store (ic->result);
}

static void arithmetic_result (iCode *ic)
{
  iCode *branch = comparison_branch (ic);
  if (!branch) { store (ic->result); return; }
  unsigned size = width (ic->result);
  if (size >= 4) emit ("\tlda (__hireg)\n\tori a,b\n");
  if (size == 6) emit ("\tlda (__cpu6_mid48)\n\tori a,b\n");
  else if (size == 1) emit ("\torib bl,bl\n");
  else emit ("\tori b,b\n");
  jump_condition (NE_OP, true, branch, false);
}

/* Fixed compiler-private frame words. Preserve both operands and X even in
   a large frame; pushed counts any temporary operand snapshots above S. */
static void private_word (const char *instruction, unsigned offset)
{
  unsigned pos = private_base + offset + pushed;
  if (pos <= 127) emit ("\t%s %u(s)\n", instruction, pos);
  else {
    emit ("\tstx (-s)\n\tldx %u\n\tadd s,x\n\t%s (x)\n\tldx (s+)\n",
          pos + 2, instruction);
  }
}

static cpu6_div_pair *division_pair (iCode *ic)
{
  for (cpu6_div_pair *pair = div_pairs; pair; pair = pair->next)
    if (pair->first == ic || pair->second == ic) return pair;
  return NULL;
}

static bool same_div_operand (operand *a, operand *b)
{
  if (!a || !b || width (a) != width (b) || unsigned_op (a) != unsigned_op (b)) return false;
  if (IS_SYMOP (a) && IS_SYMOP (b)) return OP_SYMBOL (a) == OP_SYMBOL (b);
  return IS_VALOP (a) && IS_VALOP (b) && operandLitValue (a) == operandLitValue (b);
}

static bool changes_div_input (iCode *ic, iCode *first)
{
  return IS_SYMOP (ic->result) &&
    ((IS_SYMOP (first->left) && OP_SYMBOL (ic->result) == OP_SYMBOL (first->left)) ||
     (IS_SYMOP (first->right) && OP_SYMBOL (ic->result) == OP_SYMBOL (first->right)));
}

static bool volatile_div_code (iCode *ic)
{
  return isOperandVolatile (ic->left, POINTER_GET (ic)) ||
    isOperandVolatile (ic->right, false) || isOperandVolatile (ic->result, POINTER_SET (ic));
}

static void plan_divisions (iCode *chain)
{
  div_pairs = NULL; div_bytes = 0;
  if (cpu6_stack_only || cpu6_no_divmod) return;
  for (iCode *ic = chain; ic; ic = ic->next) {
    current_ic = ic;
    if ((ic->op != '/' && ic->op != '%') || division_pair (ic) || volatile_div_code (ic)) continue;
    unsigned size = width (ic->left);
    if ((size != 2 && size != 4) || width (ic->right) != size || width (ic->result) > size ||
        changes_div_input (ic, ic) || (size == 4 && (cpu6_no_wide_native || optimize.codeSize))) continue;
    if (size == 2 && unsigned_op (ic->left) && IS_VALOP (ic->right)) {
      unsigned divisor = (unsigned)operandLitValue (ic->right) & 65535;
      if (!divisor || !(divisor & (divisor - 1))) continue; /* shifts/masks are cheaper */
    }
    unsigned distance = 0;
    for (iCode *other = ic->next; other && distance++ < 24; other = other->next) {
      if (volatile_div_code (other) || POINTER_SET (other)) break;
      if ((other->op == '/' || other->op == '%') && other->op != ic->op &&
          !division_pair (other) && same_div_operand (ic->left, other->left) &&
          same_div_operand (ic->right, other->right) && width (other->result) <= size) {
        cpu6_div_pair *pair = calloc (1, sizeof (*pair));
        wassert (pair);
        *pair = (cpu6_div_pair){ic, other, size, div_bytes, div_pairs};
        div_pairs = pair; div_bytes += size;
        break;
      }
      if (changes_div_input (other, ic)) break;
      switch (other->op) {
        case '=': case CAST: case ADDRESS_OF: case GET_VALUE_AT_ADDRESS:
        case '+': case '-': case '*': case BITWISEAND: case '|': case '^':
        case LEFT_OP: case RIGHT_OP: break;
        default: other = NULL; break; /* control flow, calls and unmodeled effects */
      }
      if (!other) break;
    }
  }
}

static void paired_word_division (iCode *ic, cpu6_div_pair *pair)
{
  load_word_a (ic->left); load (ic->right, 2);
  if (unsigned_op (ic->left)) {
    emit ("\tdiv b,a\n");
    private_word (ic->op == '/' ? "sta" : "stb", pair->offset);
    if (ic->op == '%') emit ("\txab\n");
  } else {
    unsigned a_positive = local_label++, b_positive = local_label++;
    unsigned r_positive = local_label++, q_positive = local_label++;
    emit ("\tsta (-s)\n\tore b,a\n\tsta (-s)\n\tlda 2(s)\n"); pushed += 4;
    emit ("\tori a,a\n\tbp L%u\n\tiva\n\tina\nL%u:\n", a_positive, a_positive);
    emit ("\tori b,b\n\tbp L%u\n\tivr b\n\tinr b\nL%u:\n", b_positive, b_positive);
    emit ("\tdiv b,a\n\tstb (-s)\n\txab\n"); pushed += 2;
    emit ("\tlda 4(s)\n\tbp L%u\n\tivr b\n\tinr b\nL%u:\n", r_positive, r_positive);
    emit ("\tstb (-s)\n\tldb 2(s)\n"); pushed += 2;
    emit ("\tlda 4(s)\n\tbp L%u\n\tivr b\n\tinr b\nL%u:\n", q_positive, q_positive);
    if (ic->op == '/') { emit ("\tlda (s)\n"); private_word ("sta", pair->offset); }
    else { private_word ("stb", pair->offset); emit ("\tldb (s)\n"); }
    emit ("\tlda 8\n\tadd a,s\n"); pushed -= 8;
  }
  b_cached = NULL;
  arithmetic_result (ic);
}

static void constant_long_shift (iCode *ic, unsigned count)
{
  bool left = ic->op == LEFT_OP, unsign = unsigned_op (ic->left);
  load (ic->left, 4);
  emit ("\tlda (__hireg)\n");
  if (count >= 16) {
    count -= 16;
    if (left) {
      emit ("\txfr b,a\n\tclr b\n");
      if (count >= 8) { emit ("\txfrb al,ah\n\tclrb al\n"); count -= 8; }
      if (count) emit ("\tslr a,%u\n", count);
    } else {
      emit ("\txfr a,b\n");
      if (count >= 8) { emit ("\txfrb bh,bl\n"); extend_byte (unsign); count -= 8; }
      if (count && unsign) { emit ("\trl\n\trrr b\n"); count--; }
      if (count) emit ("\tsrr b,%u\n", count);
      emit ("\tcla\n");
      if (!unsign) {
        unsigned positive = local_label++;
        emit ("\tori b,b\n\tbp L%u\n\tdca\nL%u:\n", positive, positive);
      }
    }
  } else {
    if (count >= 8) {
      count -= 8;
      if (left) emit ("\txfrb al,ah\n\txfrb bh,al\n\txfrb bl,bh\n\tclrb bl\n");
      else {
        emit ("\txfrb bh,bl\n\txfrb al,bh\n\txfrb ah,al\n\tclrb ah\n");
        if (!unsign) {
          unsigned positive = local_label++;
          emit ("\torib al,al\n\tbp L%u\n\tdcrb ah\nL%u:\n", positive, positive);
        }
      }
    }
    while (count--) {
      if (left) emit ("\tslr b\n\trlr a\n");
      else emit (unsign ? "\trl\n\trrr a\n\trrr b\n" : "\tsrr a\n\trrr b\n");
    }
  }
  emit ("\tsta (__hireg)\n");
  b_cached = NULL;
  arithmetic_result (ic);
}

static bool inplace_wide (iCode *ic)
{
  if (cpu6_no_inplace_wide || cpu6_no_wide_native || optimize.codeSize ||
      !IS_TRUE_SYMOP (ic->left) || !IS_VALOP (ic->right) || volatile_div_code (ic)) return false;
  unsigned size = width (ic->left);
  if ((size != 4 && size != 6) || width (ic->result) != size) return false;
  bool shift = ic->op == LEFT_OP || ic->op == RIGHT_OP;
  if (shift ? operandLitValue (ic->right) != 1 :
      ((ic->op != '+' && ic->op != '-') || operandLitValue (ic->right) <= 0 || operandLitValue (ic->right) > 65535))
    return false;
  symbol *sym = OP_SYMBOL (ic->left);
  iCode *assignment = NULL;
  if (!IS_SYMOP (ic->result) || OP_SYMBOL (ic->result) != sym) {
    assignment = ic->next;
    if (!IS_ITEMP (ic->result) || bitVectnBitsOn (OP_USES (ic->result)) != 1 ||
        bitVectnBitsOn (OP_DEFS (ic->result)) != 1 || !assignment || assignment->op != '=' ||
        !IS_SYMOP (assignment->result) || OP_SYMBOL (assignment->result) != sym ||
        !IS_SYMOP (assignment->right) || OP_SYMBOL (assignment->right) != OP_SYMBOL (ic->result) ||
        volatile_div_code (assignment)) return false;
  }
  if (shift) {
    /* Do not form an address between carry-chain words. Large, uncovered
       frames retain the ordinary path until a single base is profitable. */
    int pos = stack_offset (sym), zpos = pos - pushed - (int)frame_center;
    bool s = stacked (sym) && pos >= -128 && pos + (int)size - 2 <= 127;
    bool z = stacked (sym) && frame_base && zpos >= -128 && zpos + (int)size - 2 <= 127;
    if (stacked (sym) && !s && !z) return false;
    for (unsigned n = 0; n < size / 2; n++) {
      unsigned offset = ic->op == LEFT_OP ? size - 2 - 2 * n : 2 * n;
      char mem[400];
      if (!stacked (sym)) snprintf (mem, sizeof (mem), "(%s+%u)", symbol_name (sym), offset);
      else snprintf (mem, sizeof (mem), "%d(%c)", (s ? pos : zpos) + (int)offset, s ? 's' : 'z');
      emit ("\tlda %s\n", mem);
      if (ic->op == LEFT_OP) emit (n ? "\trlr a\n" : "\tsla\n");
      else if (n) emit ("\trrr a\n");
      else emit (unsigned_op (ic->left) ? "\trl\n\trrr a\n" : "\tsra\n");
      emit ("\tsta %s\n", mem);
    }
  } else {
    bool add = ic->op == '+';
    unsigned done = local_label++;
    char mem[400];
    memory_operand (sym, size - 2, mem, sizeof (mem));
    emit ("\tldb %s\n\tlda %u\n", mem, (unsigned)operandLitValue (ic->right));
    emit (add ? "\taab\n" : "\tsub b,a\n\txab\n");
    emit ("\tstb %s\n", mem); memory_done ();
    emit (add ? "\tbnl L%u\n" : "\tbl L%u\n", done);
    for (int offset = size - 4; offset >= 0; offset -= 2) {
      memory_operand (sym, offset, mem, sizeof (mem));
      emit ("\tlda %s\n\t%s\n\tsta %s\n", mem, add ? "ina" : "dca", mem);
      memory_done ();
      if (offset) {
        if (add) emit ("\tori a,a\n\tbnz L%u\n", done); /* INC preserves L; wrapping is detected by zero */
        else emit ("\tina\n\tbnz L%u\n", done); /* original word nonzero: no further borrow */
      }
    }
    emit ("L%u:\n", done);
  }
  emit ("; CPU6 direct nonvolatile multiword update\n");
  if (assignment) assignment->generated = 1;
  b_cached = NULL;
  return true;
}

static void arithmetic (iCode *ic)
{
  if (IS_FLOAT (operandType (ic->left)) || IS_FLOAT (operandType (ic->right)))
    unsupported ("unlowered float arithmetic");
  unsigned size = width (ic->result);
  if (width (ic->left) > size) size = width (ic->left);
  if (ic->op != LEFT_OP && ic->op != RIGHT_OP && width (ic->right) > size) size = width (ic->right);
  const char *helper = NULL;
  bool unsign = unsigned_op (ic->left);
  if (inplace_wide (ic)) return;
  cpu6_div_pair *pair = division_pair (ic);
  if (pair && pair->second == ic) {
    emit ("; CPU6 reuse paired quotient/remainder\n");
    if (pair->size == 4) {
      private_word ("lda", pair->offset); emit ("\tsta (__hireg)\n");
    }
    private_word ("ldb", pair->offset + pair->size - 2);
    b_cached = NULL; arithmetic_result (ic); return;
  }
  if (pair && size <= 2) { paired_word_division (ic, pair); return; }
  if (size == 4 && !cpu6_no_wide_native && !cpu6_no_wide_shifts &&
      (ic->op == LEFT_OP || ic->op == RIGHT_OP) && IS_VALOP (ic->right) &&
      (!optimize.codeSize || operandLitValue (ic->right) == 16 || operandLitValue (ic->right) == 24) &&
      operandLitValue (ic->right) >= 0 && operandLitValue (ic->right) < 32) {
    constant_long_shift (ic, (unsigned)operandLitValue (ic->right)); return;
  }
  if (!cpu6_no_byte_arithmetic && width (ic->result) == 1 && !IS_BOOL (operandType (ic->result)) &&
      size <= 2 && IS_INTEGRAL (operandType (ic->left)) && IS_INTEGRAL (operandType (ic->right)) &&
      (ic->op == '+' || ic->op == '-' || ic->op == BITWISEAND || ic->op == '|' || ic->op == '^')) {
    /* The low eight bits of these operations do not depend on upper bits.
       Signed/unsigned promotion is still applied when the result is reused. */
    if ((ic->op == '+' || ic->op == '-') && IS_VALOP (ic->right) && operandLitValue (ic->right) == 1) {
      load_low_byte (ic->left, 'b');
      emit (ic->op == '+' ? "\tinrb bl\n" : "\tdcrb bl\n");
      b_cached = NULL;
      arithmetic_result (ic);
      return;
    }
    load_low_byte (ic->left, 'a');
    load_low_byte (ic->right, 'b');
    const char *instruction = ic->op == '+' ? "addb" : ic->op == '-' ? "subb" :
                              ic->op == BITWISEAND ? "andb" : ic->op == '|' ? "orib" : "oreb";
    emit ("\t%s al,bl\n", instruction);
    b_cached = NULL;
    arithmetic_result (ic);
    return;
  }
  if (size == 6) { arithmetic48 (ic); arithmetic_result (ic); return; }
  if (size == 4 && !cpu6_no_wide_native && IS_VALOP (ic->right) &&
      (ic->op == BITWISEAND || ic->op == '|' || ic->op == '^')) {
    uint32_t mask = (uint32_t)operandLitValueUll (ic->right);
    unsigned hi = mask >> 16, lo = mask & 65535u;
    unsigned identity = ic->op == BITWISEAND ? 65535u : 0;
    const char *mnemonic = ic->op == BITWISEAND ? "and" : ic->op == '|' ? "ori" : "ore";
    if (hi == identity || lo == identity) {
      load (ic->left, 4);
      if (lo != identity) emit ("\tlda %u\n\t%s a,b\n", lo, mnemonic);
      if (hi != identity) {
        bool save_x = register_needed ('x');
        if (save_x) emit ("\tstx (-s)\n");
        emit ("\tlda (__hireg)\n\tldx %u\n\t%s x,a\n\tsta (__hireg)\n", hi, mnemonic);
        if (save_x) emit ("\tldx (s+)\n");
      }
      b_cached = NULL;
      arithmetic_result (ic);
      return;
    }
  }
  if (size == 4 && !cpu6_no_wide_native && !optimize.codeSize &&
      (ic->op == '+' || ic->op == '-') && IS_VALOP (ic->right) &&
      operandLitValue (ic->right) >= 0 && operandLitValue (ic->right) <= 65535) {
    unsigned value = (unsigned)operandLitValue (ic->right);
    load (ic->left, 4);
    if (value) {
      unsigned done = local_label++;
      emit ("\tlda %u\n", value);
      emit (ic->op == '+' ? "\taab\n\tbnl L%u\n" : "\tsub b,a\n\txab\n\tbl L%u\n", done);
      emit ("\tlda (__hireg)\n");
      emit (ic->op == '+' ? "\tina\n" : "\tdca\n");
      emit ("\tsta (__hireg)\nL%u:\n", done);
    }
    b_cached = NULL;
    arithmetic_result (ic);
    return;
  }
  if (size == 4 && !cpu6_no_wide_native && !optimize.codeSize &&
      (ic->op == '+' || ic->op == '-' || ic->op == BITWISEAND || ic->op == '|' || ic->op == '^') &&
      split_long_operand (ic->left) && split_long_operand (ic->right)) {
    b_cached = NULL;
    const char *instruction = ic->op == '+' ? "aab" : ic->op == '-' ? "sab" :
                              ic->op == BITWISEAND ? "nab" : ic->op == '|' ? "ori a,b" : "ore a,b";
    load_long_part (ic->left, 2, 'a'); load_long_part (ic->right, 2, 'b');
    emit ("\t%s\n\tstb (-s)\n", instruction); pushed += 2;
    if (ic->op == '+' || ic->op == '-') {
      unsigned no_carry = local_label++, join = local_label++;
      emit (ic->op == '+' ? "\tbnl L%u\n" : "\tbl L%u\n", no_carry);
      load_long_part (ic->left, 0, 'a'); load_long_part (ic->right, 0, 'b');
      emit ("\t%s\n", instruction);
      emit (ic->op == '+' ? "\tinr b\n" : "\tdcr b\n");
      emit ("\tbra L%u\nL%u:\n", join, no_carry);
      load_long_part (ic->left, 0, 'a'); load_long_part (ic->right, 0, 'b');
      emit ("\t%s\nL%u:\n", instruction, join);
    } else {
      load_long_part (ic->left, 0, 'a'); load_long_part (ic->right, 0, 'b');
      emit ("\t%s\n", instruction);
    }
    emit ("\tstb (__hireg)\n\tldb (s+)\n"); pushed -= 2;
    arithmetic_result (ic);
    return;
  }
  if (size == 4 && (ic->op == '/' || ic->op == '%') &&
      !cpu6_no_wide_native && !optimize.codeSize) {
    /* DRM operates on signed, big-endian memory operands. A leading zero
       byte gives the complete unsigned 32-bit range without normalization.
       Keep all buffers private to this frame and preserve the allocated X. */
    push (ic->left, 4);
    if (unsign) { emit ("\tcla\n\tsta (-s)\n"); pushed += 2; }
    push (ic->right, 4);
    if (unsign) { emit ("\tcla\n\tsta (-s)\n"); pushed += 2; }
    emit ("\tstx (-s)\n"); pushed += 2;
    unsigned scratch = unsign ? 6 : 4;
    unsigned numerator = unsign ? 15 : 10, divisor = unsign ? 9 : 6;
    unsigned remainder = unsign ? 1 : 0, bytes = unsign ? 20 : 14;
    emit ("\tlda %u\n\tadd a,s\n", (65536 - scratch) & 65535);
    pushed += scratch;
    emit ("\tldx %u\n\tadd s,x\n\tldb %u\n\tadd s,b\n", numerator, divisor);
    emit ("\tlda %u\n\tadd s,a\n\trf\n", remainder);
    emit ("\t.byte 0x46,0x%02x,0x7a,0x24\n", unsign ? 0x44 : 0x33);
    if (pair) {
      unsigned alternate = (ic->op == '/' ? remainder : numerator) + (unsign ? 1 : 0);
      emit ("\tlda %u(s)\n", alternate); private_word ("sta", pair->offset);
      emit ("\tlda %u(s)\n", alternate + 2); private_word ("sta", pair->offset + 2);
    }
    unsigned result = ic->op == '/' ? numerator : remainder;
    if (unsign) result++; /* Skip the zero-extension byte. */
    emit ("\tlda %u(s)\n\tsta (__hireg)\n\tldb %u(s)\n", result, result + 2);
    emit ("\tldx %u(s)\n\tlda %u\n\tadd a,s\n", scratch, bytes);
    pushed -= bytes;
    b_cached = NULL;
    arithmetic_result (ic);
    return;
  }
  if (size <= 2 && IS_VALOP (ic->right)) {
    unsigned value = (unsigned)(long long)operandLitValue (ic->right) & 65535;
    if (ic->op == '*') {
      load (ic->left, 2);
      if (!value) emit ("\tldb 0\n");
      else if (value != 1) {
        unsigned bit = 0x8000, shifts = 0, cost = 15;
        while (!(value & bit)) bit >>= 1;
        for (unsigned scan = bit >> 1; scan; scan >>= 1) {
          shifts++;
          if (value & scan) { cost += 15 + 5 * shifts + 9; shifts = 0; }
        }
        if (shifts) cost += 15 + 5 * shifts;
        /* Measured microcode costs: XFR B,A=15, SLR B,n=15+5n, AAB=9,
           immediate MUL=116. Combine consecutive shifts before comparing. */
        if (optimize.codeSize || cost >= 116) emit ("\tmul %u,b\n", value);
        else {
          emit ("\txfr b,a\n");
          shifts = 0;
          while ((bit >>= 1)) {
            shifts++;
            if (value & bit) {
              emit ("\tslr b,%u\n\taab\n", shifts);
              shifts = 0;
            }
          }
          if (shifts) emit ("\tslr b,%u\n", shifts);
        }
      }
      arithmetic_result (ic);
      return;
    }
    if ((ic->op == '/' || ic->op == '%') && unsign && value) {
      load (ic->left, 2);
      if (value == 1) {
        if (ic->op == '%') emit ("\tldb 0\n");
      } else if (!(value & (value - 1))) {
        if (ic->op == '%') emit ("\tlda %u\n\tnab\n", value - 1);
        else {
          unsigned count = 0;
          while ((value >>= 1)) count++;
          if (count >= 8) {
            emit ("\txfrb bh,bl\n\tclrb bh\n");
            count -= 8;
          } else {
            emit ("\trl\n\trrr b\n");
            count--;
          }
          if (count) emit ("\tsrr b,%u\n", count);
        }
      } else {
        if (ic->op == '/') emit ("\tdiv %u,b\n", value);
        else emit ("\tdiv b,%u,a\n\txab\n", value);
      }
      arithmetic_result (ic);
      return;
    }
    if (ic->op == LEFT_OP || ic->op == RIGHT_OP) {
      load (ic->left, 2);
      bool logical_first = unsign && width (ic->left) > 1 && value < 8;
      if (value >= 8) {
        if (ic->op == LEFT_OP) emit ("\txfrb bl,bh\n\tclrb bl\n");
        else {
          emit ("\txfrb bh,bl\n");
          extend_byte (unsign);
        }
        value -= 8;
      }
      struct valinfo source = word_info (ic, ic->left);
      bool positive = !source.anything && !source.nothing &&
        ((source.min >= 0 && source.max <= 32767) ||
         (source.knownbitsmask & ~source.knownbits & 0x8000u));
      if (ic->op == RIGHT_OP && logical_first && value && !positive) {
        /* One logical step makes the sign bit zero. Subsequent arithmetic
           right shifts therefore remain logical, without re-clearing L. */
        emit ("\trl\n\trrr b\n");
        value--;
      }
      if (value && value <= 16)
        emit (ic->op == LEFT_OP ? "\tslr b,%u\n" : "\tsrr b,%u\n", value);
      else for (unsigned n = 0; n < value; n++)
        emit (ic->op == LEFT_OP ? "\tslr b\n" : "\tsrr b\n");
      arithmetic_result (ic);
      return;
    }
    if (ic->op == '+' || ic->op == '-' || ic->op == BITWISEAND || ic->op == '|' || ic->op == '^') {
      load (ic->left, 2);
      if ((ic->op == '+' || ic->op == '-') && value <= 16) {
        if (value == 1) emit (ic->op == '+' ? "\tinr b\n" : "\tdcr b\n");
        if (value == 2 && IS_PTR (operandType (ic->result)))
          emit (ic->op == '+' ? "\tinr b\n\tinr b\n" : "\tdcr b\n\tdcr b\n");
        else if (value > 1) emit (ic->op == '+' ? "\tinr b,%u\n" : "\tdcr b,%u\n", value);
      } else {
        emit ("\tlda %u\n", value);
        switch (ic->op) {
          case '+': emit ("\taab\n"); break;
          case '-': emit ("\tsub b,a\n\txab\n"); break;
          case BITWISEAND: emit ("\tnab\n"); break;
          case '|': emit ("\tori a,b\n"); break;
          case '^': emit ("\tore a,b\n"); break;
        }
      }
      arithmetic_result (ic);
      return;
    }
  }
  if (size <= 2 && (ic->op == '*' || ic->op == '/' || ic->op == '%')) {
    load_word_a (ic->left);
    load (ic->right, 2);
    if (ic->op == '*') emit ("\tmul a,b\n");
    else if (unsign) {
      emit ("\tdiv b,a\n"); /* remainder in A, quotient in B */
      if (ic->op == '%') emit ("\txab\n");
    } else {
      unsigned positive_a = local_label++, positive_b = local_label++, positive_result = local_label++;
      unsigned bytes = ic->op == '/' ? 4 : 2;
      emit ("\tsta (-s)\n");
      if (ic->op == '/') emit ("\tore b,a\n\tsta (-s)\n\tlda 2(s)\n");
      pushed += bytes;
      emit ("\tori a,a\n\tbp L%u\n\tiva\n\tina\nL%u:\n", positive_a, positive_a);
      emit ("\tori b,b\n\tbp L%u\n\tivr b\n\tinr b\nL%u:\n", positive_b, positive_b);
      emit ("\tdiv b,a\n");
      if (ic->op == '%') emit ("\txab\n");
      /* Quotient takes the XOR of signs; remainder takes the dividend sign. */
      emit ("\tlda (s)\n\tbp L%u\n\tivr b\n\tinr b\nL%u:\n", positive_result, positive_result);
      emit ("\tlda %u\n\tadd a,s\n", bytes);
      pushed -= bytes;
    }
    arithmetic_result (ic);
    return;
  }
  if (size == 4 && ic->op == '*' && !optimize.codeSize) {
    /* Low 32 bits: LL*RL + ((LH*RL + LL*RH) << 16). No callee-saved
       register is touched, and the inputs survive in private stack words. */
    push (ic->left, 4);
    load (ic->right, 4);
    emit ("\tstb (-s)\n\tlda (__hireg)\n\tsta (-s)\n");
    pushed += 4;
    emit ("\tlda 6(s)\n\tldb 2(s)\n\tmul b,a\n\tsta (__hireg)\n\tstb (-s)\n");
    pushed += 2;
    emit ("\tlda 8(s)\n\tldb 2(s)\n\tmul a,b\n\tlda (__hireg)\n\taab\n\tstb (__hireg)\n");
    emit ("\tlda 6(s)\n\tldb 4(s)\n\tmul a,b\n\tlda (__hireg)\n\taab\n\tstb (__hireg)\n");
    emit ("\tldb (s+)\n\tlda 8\n\tadd a,s\n");
    pushed -= 10;
    arithmetic_result (ic);
    return;
  }
  switch (ic->op) {
    case '*': helper = size == 4 ? "__mull" : "__mul"; break;
    case '/': helper = size == 4 ? (unsign ? "__divul" : "__divl") : (unsign ? "__divu" : "__div"); break;
    case '%': helper = size == 4 ? (unsign ? "__remul" : "__reml") : (unsign ? "__remu" : "__rem"); break;
    case LEFT_OP: helper = size == 4 ? "__shll" : "__shl"; break;
    case RIGHT_OP: helper = size == 4 ? (unsign ? "__shrul" : "__shrl") : (unsign ? "__shru" : "__shr"); break;
  }
  if (size == 4 && !helper) {
    switch (ic->op) {
      case '+': helper = "__plusl"; break;
      case '-': helper = "__minusl"; break;
      case BITWISEAND: helper = "__bandl"; break;
      case '|': helper = "__orl"; break;
      case '^': helper = "__xorl"; break;
    }
  }
  if (helper) {
    push (ic->left, size == 4 ? 4 : 2);
    load (ic->right, ic->op == LEFT_OP || ic->op == RIGHT_OP ? 2 : (size == 4 ? 4 : 2));
    emit ("\tjsr %s\n", helper);
    pushed -= size == 4 ? 4 : 2;
  } else {
    char reg = ic->op == '-' ? 0 : word_register (ic->right);
    operand *other = ic->left;
    if (!reg && ic->op != '-') { reg = word_register (ic->left); other = ic->right; }
    if (reg) {
      const char *mnemonic = ic->op == '+' ? "add" : ic->op == BITWISEAND ? "and" :
                             ic->op == '|' ? "ori" : ic->op == '^' ? "ore" : NULL;
      if (!mnemonic) unsupported ("register arithmetic operation");
      load (other, 2);
      emit ("\t%s %c,b\n", mnemonic, reg);
      arithmetic_result (ic);
      return;
    }
    load_word_a (ic->left);
    load (ic->right, 2);
    switch (ic->op) {
      case '+': emit ("\taab\n"); break;
      case '-': emit ("\tsab\n"); break;
      case BITWISEAND: emit ("\tnab\n"); break;
      case '|': emit ("\tori a,b\n"); break;
      case '^': emit ("\tore a,b\n"); break;
      default: unsupported ("arithmetic operation");
    }
  }
  arithmetic_result (ic);
}

/* A static symbol, or the same address register, can serve every word of
   a wide access. Offsets are bytes in big-endian order. */
static void pointer_access (const char *mnemonic, cpu6_slot *slot, char reg, int offset)
{
  if (slot && slot->address_base)
    emit ("\t%s (%s+%u)\n", mnemonic, symbol_name (slot->address_base),
          (unsigned)(uint16_t)(slot->address_offset + offset));
  else if (offset)
    emit ("\t%s %d(%c)\n", mnemonic, offset, reg);
  else
    emit ("\t%s (%c)\n", mnemonic, reg);
}

static void pointer_get (iCode *ic)
{
  unsigned size = width (ic->result);
  if (IS_BITFIELD (operandType (ic->result))) unsupported ("bitfield access");
  int offset = ic->right ? (int)operandLitValue (ic->right) : 0;
  cpu6_slot *slot = IS_SYMOP (ic->left) ? slot_for (OP_SYMBOL (ic->left)) : NULL;
  char reg = word_register (ic->left);
  if (!(slot && slot->address_base) && (!reg || offset < -128 || offset > 123)) {
    load (ic->left, 2);
    reg = 'b';
    if (offset < -128 || offset > 123) {
      emit ("\tlda %u\n\taab\n", (unsigned)offset & 65535);
      offset = 0;
    }
  }
  if (size >= 4) {
    pointer_access ("lda", slot, reg, offset);
    emit ("\tsta (__hireg)\n");
    if (size == 6) {
      pointer_access ("lda", slot, reg, offset + 2);
      emit ("\tsta (__cpu6_mid48)\n");
    }
  }
  pointer_access (size == 1 ? "ldbb" : "ldb", slot, reg, offset + (size >= 4 ? size - 2 : 0));
  b_cached = NULL;
  store (ic->result);
}

static void pointer_set (iCode *ic)
{
  sym_link *target = operandType (ic->result);
  if (IS_PTR (target) && IS_BITFIELD (target->next))
    unsupported ("bitfield access");

  unsigned size = width (ic->right);
  int offset = ic->left ? (int)operandLitValue (ic->left) : 0;
  cpu6_slot *slot = IS_SYMOP (ic->result) ? slot_for (OP_SYMBOL (ic->result)) : NULL;
  char reg = word_register (ic->result);
  bool stacked_pointer = !reg && !(slot && slot->address_base) && size >= 4;
  bool save_x = stacked_pointer && register_needed ('x');
  if (save_x) { emit ("\tstx (-s)\n"); pushed += 2; }
  if (!reg && !(slot && slot->address_base)) {
    load (ic->result, 2);
    if (stacked_pointer) { emit ("\tstb (-s)\n"); pushed += 2; reg = 'x'; }
    else { emit ("\txfr b,a\n"); reg = 'a'; }
  }
  if (size == 1 && !cpu6_no_byte_arithmetic) load_low_byte (ic->right, 'b');
  else load (ic->right, size);
  if (stacked_pointer) { emit ("\tldx (s+)\n"); pushed -= 2; }
  if (size >= 4) {
    emit ("\tlda (__hireg)\n");
    pointer_access ("sta", slot, reg, offset);
    if (size == 6) {
      emit ("\tlda (__cpu6_mid48)\n");
      pointer_access ("sta", slot, reg, offset + 2);
    }
  }
  pointer_access (size == 1 ? "stbb" : "stb", slot, reg, offset + (size >= 4 ? size - 2 : 0));
  if (save_x) { emit ("\tldx (s+)\n"); pushed -= 2; }
}

static void adjust_frame (int delta, char scratch)
{
  if (!delta) return;
  if (delta >= -16 && delta <= 16)
    emit (delta > 0 ? "\tinr s,%u\n" : "\tdcr s,%u\n", (unsigned)abs (delta));
  else
    emit ("\tld%c %u\n\tadd %c,s\n", scratch, (unsigned)(uint16_t)delta, scratch);
}

static void return_frame (void)
{
  adjust_frame (frame, 'a');
  if (use_z) emit ("\tlda (s+)\n\txfr a,z\n");
  if (use_y) emit ("\tlda (s+)\n\txfr a,y\n");
  emit ("\tldx (s+)\n");
}

/* Follow only control-flow nodes with no observable work after the call.
   Void functions often reach ENDFUNCTION without an explicit RETURN iCode. */
static bool returns_void_after (iCode *node)
{
  for (unsigned steps = 0; node && steps < 128; steps++) {
    if (node->op == RETURN) return !node->left || IS_VOID (operandType (node->left));
    if (node->op == ENDFUNCTION) return true;
    if (node->op == LABEL) { node = node->next; continue; }
    if (node->op == GOTO) {
      symbol *target = node->label;
      for (node = function_chain; node; node = node->next)
        if (node->op == LABEL && node->label->key == target->key) break;
      continue;
    }
    return false;
  }
  return false;
}

static bool self_tail_site (iCode *ic)
{
  if (cpu6_stack_only || cpu6_no_tail_recursion || local_address_taken ||
      FUNC_SDCCCALL (currFunc->type) != 0 ||
      IFFUNC_HASVARARGS (currFunc->type) || ic->op != CALL ||
      !IS_SYMOP (ic->left) || OP_SYMBOL (ic->left) != currFunc)
    return false;
  if (IS_VOID (currFunc->type->next)) {
    if (!returns_void_after (ic->next)) return false;
  } else if (!ic->next || ic->next->op != RETURN || !IS_SYMOP (ic->result) ||
             !IS_SYMOP (ic->next->left) || OP_SYMBOL (ic->result) != OP_SYMBOL (ic->next->left))
    return false;
  unsigned bytes = 0;
  for (value *arg = FUNC_ARGS (currFunc->type); arg; arg = arg->next) {
    unsigned size = IS_ARRAY (arg->type) ? 2 : getSize (arg->type);
    if ((!IS_INTEGRAL (arg->type) && !IS_PTR (arg->type) && !IS_ARRAY (arg->type)) ||
        !size || (size > 4 && !(cpu6_bitint48 && size == 6 && IS_BITINT (arg->type)))) return false;
    bytes += (size + 1) & ~1U;
  }
  return bytes == (unsigned)ic->parmBytes && frame + saved + 2 + 2 * bytes <= 65535;
}

/* A contiguous push group has no intervening evaluations. Already resident
   temporaries and literals can be copied directly at CALL. True variables
   retain their original push, preserving volatile reads and permutations. */
static void plan_tail_arguments (iCode *chain)
{
  for (iCode *ic = chain; ic; ic = ic->next) {
    if (!self_tail_site (ic)) continue;
    unsigned count = 0;
    for (value *arg = FUNC_ARGS (currFunc->type); arg; arg = arg->next) count++;
    if (!count) continue;
    cpu6_tail_site *site = calloc (1, sizeof (*site));
    wassert (site);
    site->args = calloc (count, sizeof (*site->args));
    wassert (site->args);
    site->call = ic;
    iCode *push = ic->prev;
    unsigned offset = 0;
    bool valid = true, any_direct = false;
    for (value *arg = FUNC_ARGS (currFunc->type); arg; arg = arg->next) {
      if (!push || push->op != IPUSH || !push->parmPush || !arg->sym || !arg->sym->onStack) {
        valid = false; break;
      }
      unsigned size = (getSize (arg->type) + 1) & ~1U;
      unsigned actual = (width (push->left) + 1) & ~1U;
      if (size != actual) { valid = false; break; }
      cpu6_slot *slot = IS_ITEMP (push->left) ? slot_for (OP_SYMBOL (push->left)) : NULL;
      bool direct = IS_VALOP (push->left) || (slot && !slot->transient && !slot->sym->addrtaken);
      site->args[site->count++] = (cpu6_tail_arg){push, arg->sym, size, offset, direct};
      if (!direct) site->stack_bytes += size;
      any_direct |= direct;
      offset += size;
      push = push->prev;
    }
    if (!valid || !any_direct || offset != (unsigned)ic->parmBytes) {
      free (site->args); free (site); continue;
    }
    for (unsigned i = 0; i < site->count; i++)
      if (site->args[i].direct) site->args[i].push->generated = 1;
    site->next = tail_sites;
    tail_sites = site;
  }
}

static void copy_tail_words (unsigned bytes, unsigned argument_offset)
{
  unsigned destination = pushed + frame + saved + argument_offset;
  /* Argument expressions have all been evaluated and pushed already.
     Copy that separate snapshot into the incoming argument area. This
     preserves swaps, byte padding and 32-bit values without serializing
     parallel assignments such as recurse(b, a). The regions do not overlap. */
  if (bytes && (destination > 127 || bytes >= 16)) {
    /* X is dead at the terminal call; its original return link remains in
       the saved frame. Use postincrement for larger or distant blocks. */
    emit ("\tldx %u\n\tadd s,x\n", destination + 2);
    for (unsigned offset = 0; offset < bytes; offset += 2)
      emit ("\tldb (s+)\n\tstb (x+)\n");
  } else {
    /* Popping each source word advances S alongside the destination, so
       the displacement stays constant and no final stack adjustment is needed. */
    for (unsigned offset = 0; offset < bytes; offset += 2)
      emit ("\tldb (s+)\n\tstb %u(s)\n", destination);
  }
  pushed -= bytes;
}

static bool self_tail_call (iCode *ic)
{
  if (!tail_body_label || !self_tail_site (ic)) return false;
  cpu6_tail_site *site;
  for (site = tail_sites; site && site->call != ic; site = site->next) { }
  if (!site && pushed != ic->parmBytes) return false;
  emit ("; CPU6 tail recursion: reuse frame and replace argument state\n");
  if (site) {
    if (pushed != (int)site->stack_bytes) unsupported ("tail argument snapshot mismatch");
    /* All deferred sources remain alive in allocated registers/frame slots.
       Preserve X during distant stores until every deferred value is copied. */
    for (unsigned i = 0; i < site->count; i++) {
      cpu6_tail_arg *arg = site->args + i;
      if (!arg->direct) continue;
      load (arg->push->left, arg->size);
      char mem[400];
      if (arg->size >= 4) {
        memory_operand (arg->parameter, 0, mem, sizeof (mem));
        emit ("\tlda (__hireg)\n\tsta %s\n", mem);
        memory_done ();
        if (arg->size == 6) {
          memory_operand (arg->parameter, 2, mem, sizeof (mem));
          emit ("\tlda (__cpu6_mid48)\n\tsta %s\n", mem);
          memory_done ();
        }
      }
      memory_operand (arg->parameter, getSize (arg->parameter->type) == 1 ? -1 : arg->size >= 4 ? arg->size - 2 : 0,
                      mem, sizeof (mem));
      emit ("\tstb %s\n", mem);
      memory_done ();
    }
    for (unsigned i = 0; i < site->count;) {
      if (site->args[i].direct) { i++; continue; }
      unsigned offset = site->args[i].offset, bytes = 0;
      do { bytes += site->args[i++].size; } while (i < site->count && !site->args[i].direct);
      copy_tail_words (bytes, offset);
    }
  } else copy_tail_words (ic->parmBytes, 0);
  wassert (!pushed);
  emit ("\tjmp L%u\n", tail_body_label);
  if (!IS_VOID (currFunc->type->next)) ic->next->generated = 1;
  b_cached = NULL;
  return true;
}

static bool tail_call (iCode *ic)
{
  iCode *next = ic->next;
  if (ic->op == CALL && IS_SYMOP (ic->left) && OP_SYMBOL (ic->left) == currFunc) return false;
  /* The generic escape bits remain conservative before ralloc2. This port
     uses the stronger whole-function address-taken/inline-assembly check. */
  if (cpu6_stack_only || cpu6_no_tail_calls || local_address_taken ||
      FUNC_SDCCCALL (currFunc->type) != 0 || register_call (ic) ||
      pushed != ic->parmBytes || (ic->parmBytes && ic->op != CALL))
    return false;
  if (IS_VOID (currFunc->type->next)) {
    if (!returns_void_after (next)) return false;
  } else {
    if (!next || next->op != RETURN || !IS_SYMOP (ic->result) || !IS_SYMOP (next->left) ||
        OP_SYMBOL (ic->result) != OP_SYMBOL (next->left) ||
        width (ic->result) != getSize (currFunc->type->next)) return false;
  }
  unsigned incoming = 0;
  if (ic->parmBytes) {
    if (IFFUNC_HASVARARGS (currFunc->type)) return false;
    for (value *arg = FUNC_ARGS (currFunc->type); arg; arg = arg->next)
      incoming += ((IS_ARRAY (arg->type) ? 2 : getSize (arg->type)) + 1) & ~1U;
    if ((unsigned)ic->parmBytes > incoming) return false;
  }
  if (ic->op == CALL && !strncmp(symbol_name(OP_SYMBOL(ic->left)), "__", 2))
    return false;
  if (ic->op == PCALL) load (ic->left, 2);
  if (ic->parmBytes) {
    emit ("; CPU6 terminal call: reuse incoming argument area\n");
    copy_tail_words (ic->parmBytes, 0);
  }
  return_frame ();
  if (ic->op == PCALL) emit ("\tjmp (b)\n");
  else emit ("\tjmp %s\n", symbol_name (OP_SYMBOL (ic->left)));
  if (!IS_VOID (currFunc->type->next)) next->generated = 1;
  b_cached = NULL;
  return true;
}

static void emit_assembly (const char *text)
{
  asm_template = true;
  emit ("%s\n", text);
  asm_template = false;
  b_cached = NULL;
}

static void generate_builtin (iCode *send)
{
  operand *args[MAX_BUILTIN_ARGS];
  int count;
  iCode *call = getBuiltinParms (send, &count, args);
  const char *name = OP_SYMBOL (call->left)->name;
  if (!call->inlineAsm || ((strcmp (name, "__cpu6_asm16") || count != 1) &&
      (strcmp (name, "__cpu6_asm16_2") || count != 2)))
    unsupported ("CPU6 builtin");
  if (!cpu6OperandAsm (call->inlineAsm))
    unsupported ("operand-bound assembly (requires straight-line A/B instructions)");
  if (count == 2)
    load_word_a (args[0]);
  load (args[count - 1], 2);
  current_ic = call;
  emit_assembly (call->inlineAsm);
  if (call->result && (!IS_ITEMP (call->result) || bitVectnBitsOn (OP_USES (call->result))))
    store (call->result);
  current_ic = send;
}

static void generate (iCode *ic)
{
  if (ic->generated) return;
  if (POINTER_SET (ic)) { pointer_set (ic); return; }
  if (IS_ITEMP (ic->result)) {
    cpu6_slot *slot = slot_for (OP_SYMBOL (ic->result));
    if (slot && slot->address_base) return;
  }
  if (IS_CONDITIONAL (ic)) { compare (ic); return; }
  switch (ic->op) {
    case FUNCTION:
      b_cached = NULL;
      if (IS_FLOAT (currFunc->type->next) && !cpu6_float32) unsupported ("floating return type (enable --cpu6-float32)");
      if (getSize (currFunc->type->next) > 4 &&
          !(cpu6_bitint48 && IS_BITINT (currFunc->type->next) && getSize (currFunc->type->next) == 6))
        unsupported ("unsupported scalar return width");
      for (value *arg = FUNC_ARGS (currFunc->type); arg; arg = arg->next)
        if (!IS_ARRAY (arg->type) && getSize (arg->type) > 4 &&
            !(cpu6_bitint48 && IS_BITINT (arg->type) && getSize (arg->type) == 6))
          unsupported ("unsupported scalar parameter width");
      emit ("%s:\n\tstx (-s)\n", symbol_name (OP_SYMBOL (ic->left)));
      if (receives[0] || receives[1]) {
        /* X's return link is saved; use X as scratch so incoming A/B remain
           intact until both RECEIVE destinations have been initialized. */
        if (use_y) emit ("\txfr y,x\n\tstx (-s)\n");
        if (use_z) emit ("\txfr z,x\n\tstx (-s)\n");
        adjust_frame (-frame, 'x');
        if (frame_base) emit ("; CPU6 fixed frame window\n\tldx %u\n\tadd s,x\n\txfr x,z\n", frame_center);
        if (receives[1]) { store (receives[1]->result); receives[1]->generated = 1; }
        if (receives[0]) { emit ("\txfr a,b\n"); b_cached = NULL; store (receives[0]->result); receives[0]->generated = 1; }
      } else {
        if (use_y) emit ("\txfr y,a\n\tsta (-s)\n");
        if (use_z) emit ("\txfr z,a\n\tsta (-s)\n");
        adjust_frame (-frame, 'a');
        if (frame_base) emit ("; CPU6 fixed frame window\n\tlda %u\n\tadd s,a\n\txaz\n", frame_center);
      }
      /* Back edges enter before parameter reloads, after frame allocation. */
      if (tail_body_label) emit ("L%u:\n", tail_body_label);
      for (unsigned i = 0; i < nslots; i++)
        if (slots[i].parameter && slots[i].reg) {
          char reg = slots[i].reg;
          slots[i].reg = 0;
          load (operandFromSymbol (slots[i].sym, false), 2);
          slots[i].reg = reg;
          emit ("\txfr b,%c\n", reg);
          b_cached = slots[i].sym;
          b_cached_width = slots[i].size;
        }
      break;
    case ENDFUNCTION:
      if (pushed) unsupported ("unbalanced generated stack");
      return_frame ();
      emit ("\trsr\n");
      break;
    case RETURN:
      if (ic->left) load (ic->left, getSize (currFunc->type->next));
      emit ("\tjmp L%d\n", returnLabel->key);
      break;
    case LABEL: b_cached = NULL; emit ("L%d:\n", ic->label->key); break;
    case GOTO: b_cached = NULL; emit ("\tjmp L%d\n", ic->label->key); break;
    case JUMPTABLE: {
      /* The frontend bounds-checks and biases the index. Keep the table in
         the function so its relocations follow it into an MMU page or overlay. */
      unsigned table = local_label++;
      load (ic->left, 2);
      emit ("\tslr b\n\tlda L%u\n\taab\n\tldb (b)\n\tjmp (b)\nL%u:\n", table, table);
      for (symbol *label = setFirstItem (IC_JTLABELS (ic)); label; label = setNextItem (IC_JTLABELS (ic)))
        emit ("\t.word L%d\n", label->key);
      b_cached = NULL;
      break;
    }
    case '=':
      load (ic->right, width (ic->result)); store (ic->result); break;
    case CAST:
      if (IS_BOOL (operandType (ic->result)) && IS_FLOAT (operandType (ic->right))) {
        float_truth (ic->right); boolify (2, false); store (ic->result); break;
      }
      load (ic->right, IS_BOOL (operandType (ic->result)) ? width (ic->right) : width (ic->result));
      if (IS_BOOL (operandType (ic->result))) boolify (width (ic->right), false);
      store (ic->result); break;
    case '+': case '-': case '*': case '/': case '%':
    case BITWISEAND: case '|': case '^': case LEFT_OP: case RIGHT_OP:
      arithmetic (ic); break;
    case '!':
      if (IS_FLOAT (operandType (ic->left))) {
        float_truth (ic->left); boolify (2, true); store (ic->result); break;
      }
      load (ic->left, width (ic->left)); boolify (width (ic->left), true);
      store (ic->result); break;
    case '~':
      load (ic->left, width (ic->left));
      if (width (ic->result) == 6) {
        emit ("\tlda (__hireg)\n\tiva\n\tsta (__hireg)\n"
              "\tlda (__cpu6_mid48)\n\tiva\n\tsta (__cpu6_mid48)\n\tivr b\n");
        store (ic->result); break;
      }
      if (width (ic->result) == 4) {
        emit ("\tstb (-s)\n\tldb (__hireg)\n\tlda 65535\n\tore a,b\n\tstb (__hireg)\n\tldb (s+)\n");
      }
      emit ("\tlda 65535\n\tore a,b\n"); store (ic->result); break;
    case UNARYMINUS:
      if (IS_FLOAT (operandType (ic->result))) {
        load (ic->left, 4);
        emit ("\tstx (-s)\n\tldx 32768\n\tlda (__hireg)\n\tore x,a\n\tsta (__hireg)\n\tldx (s+)\n");
        b_cached = NULL; store (ic->result); break;
      }
      if (width (ic->result) == 6) { arithmetic48 (ic); store (ic->result); break; }
      if (width (ic->result) == 4) {
        emit ("\tcla\n\tsta (-s)\n\tsta (-s)\n"); pushed += 4;
        load (ic->left, 4); emit ("\tjsr __minusl\n"); pushed -= 4;
      } else { load (ic->left, 2); emit ("\tcla\n\tsab\n"); }
      store (ic->result); break;
    case IFX: {
      unsigned label = local_label++;
      if (IS_FLOAT (operandType (ic->left))) {
        float_truth (ic->left); emit ("\tori b,b\n");
      }
      else if (width (ic->left) >= 4) {
        load (ic->left, width (ic->left)); emit ("\tlda (__hireg)\n\tori a,b\n");
      }
      else { load (ic->left, width (ic->left)); emit ("\tori b,b\n"); }
      if (width (ic->left) == 6) emit ("\tlda (__cpu6_mid48)\n\tori a,b\n");
      if (IC_TRUE (ic)) emit ("\tbz L%u\n\tjmp L%d\nL%u:\n", label, IC_TRUE (ic)->key, label);
      else emit ("\tbnz L%u\n\tjmp L%d\nL%u:\n", label, IC_FALSE (ic)->key, label);
      b_cached = NULL;
      break;
    }
    case ADDRESS_OF:
      address (OP_SYMBOL (ic->left), ic->right ? (int)operandLitValue (ic->right) : 0);
      store (ic->result); break;
    case GET_VALUE_AT_ADDRESS: pointer_get (ic); break;
    case IPUSH:
      if (!ic->parmPush) unsupported ("non-parameter push");
      if (getSize (operandType (ic->left)) > (cpu6_bitint48 ? 6 : 4)) unsupported ("unsupported scalar argument width");
      push (ic->left, width (ic->left)); break;
    case IPUSH_VALUE_AT_ADDRESS: unsupported ("indirect argument push"); break;
    case CALL: case PCALL:
      if (self_tail_call (ic)) break;
      if (tail_call (ic)) break;
      if (register_call (ic)) {
        if (send_values[0]) {
          if (send_staged[0]) private_word ("lda", div_bytes);
          else load_word_a (send_values[0]);
        }
        if (send_values[1]) {
          if (send_staged[1]) private_word ("ldb", div_bytes + 2);
          else load (send_values[1], 2);
        }
        if (ic->op == PCALL) {
          /* Keep A, stage B and the live X value before using X as the target.
             This also works when the function pointer itself lives in X. */
          private_word ("stb", div_bytes + 2);
          emit ("\txfr x,b\n"); private_word ("stb", div_bytes + 4);
          b_cached = NULL;
          load (ic->left, 2);
          emit ("\txfr b,x\n");
          private_word ("ldb", div_bytes + 2);
          emit ("\tjsr (x)\n");
          private_word ("lda", div_bytes + 4);
          emit ("\txfr a,x\n");
        } else emit ("\tjsr %s\n", symbol_name (OP_SYMBOL (ic->left)));
      } else if (ic->op == PCALL) { load (ic->left, 2); emit ("\tjsr (b)\n"); }
      else emit ("\tjsr %s\n", symbol_name (OP_SYMBOL (ic->left)));
      send_values[0] = send_values[1] = NULL;
      send_staged[0] = send_staged[1] = false;
      b_cached = NULL;
      adjust_frame (ic->parmBytes, 'a');
      pushed -= ic->parmBytes;
      store (ic->result); break;
    case SEND:
      if (ic->builtinSEND) { generate_builtin (ic); break; }
      if (ic->argreg < 1 || ic->argreg > 2) unsupported ("register argument index");
      send_values[ic->argreg - 1] = ic->left;
      send_staged[ic->argreg - 1] = isOperandVolatile (ic->left, false);
      if (send_staged[ic->argreg - 1]) {
        load (ic->left, 2); private_word ("stb", div_bytes + 2 * (ic->argreg - 1));
      }
      break;
    case RECEIVE: unsupported ("unplanned register receive"); break;
    case DUMMY_READ_VOLATILE:
      if (ic->left) load (ic->left, width (ic->left));
      if (ic->right) load (ic->right, width (ic->right));
      break;
    case POINTER_NONNULL_CHECK: break; /* Static analysis marker, as on STM8. */
    case INLINEASM:
      inline_assembly_seen = true;
      emit_assembly (ic->inlineAsm); break;
    default:
      fprintf (stderr, "cpu6: iCode %u\n", ic->op);
      unsupported ("iCode operation");
  }
}

/* Fuse only adjacent operations: at the dereference the base must still
   denote the pointer evaluated by the addition. Keep volatile accesses and
   pointer type metadata intact for subsequent peepholes. */
static void fold_indexed_accesses (ebbIndex *ebbi)
{
  for (int block = 0; block < ebbi->count; block++) {
    eBBlock *ebb = ebbi->bbOrder[block];
    for (iCode *ic = ebb->sch; ic && ic != ebb->ech; ic = ic->next) {
      iCode *use = ic->next;
      if (ic->op != '+' || !IS_ITEMP (ic->result) || !IS_PTR (operandType (ic->result)) ||
          !IS_VALOP (ic->right) || bitVectnBitsOn (OP_USES (ic->result)) != 1 ||
          bitVectnBitsOn (OP_DEFS (ic->result)) != 1 ||
          !IS_ITEMP (ic->left) || !IS_PTR (operandType (ic->left)) ||
          !use || (!POINTER_SET (use) && use->op != GET_VALUE_AT_ADDRESS))
        continue;
      bool write = POINTER_SET (use);
      operand **addr = write ? &use->result : &use->left;
      operand **disp = write ? &use->left : &use->right;
      if (!IS_SYMOP ((*addr)) || OP_SYMBOL (*addr) != OP_SYMBOL (ic->result) ||
          (write && IS_SYMOP (use->right) && OP_SYMBOL (use->right) == OP_SYMBOL (ic->result)) ||
          (*disp && !IS_VALOP ((*disp))) || isOperandVolatile (*addr, true) ||
          isOperandVolatile (ic->left, false)) continue;
      double offset = operandLitValue (ic->right) + (*disp ? operandLitValue (*disp) : 0);
      if (offset < -128 || offset > 123) continue;
      operand *base = operandFromOperand (ic->left);
      base->isaddr = (*addr)->isaddr;
      attachiCodeOperand (base, addr, use);
      attachiCodeOperand (operandFromLit (offset), disp, use);
      detachiCodeOperand (&ic->left, ic);
      detachiCodeOperand (&ic->right, ic);
      detachiCodeOperand (&ic->result, ic);
      remiCodeFromeBBlock (ebb, ic);
    }
  }
}

void cpu6_assignRegisters (ebbIndex *ebbi)
{
  tail_sites = NULL;
  frame_base = false; frame_center = 0;
  genLine.lineHead = genLine.lineCurr = NULL;
  if (!cpu6_stack_only) fold_indexed_accesses (ebbi);
  recomputeLiveRanges (ebbi->bbOrder, ebbi->count, false);
  iCode *chain = iCodeFromeBBlock (ebbi->bbOrder, ebbi->count);
  register_scratch = 0;
  receives[0] = receives[1] = NULL;
  send_values[0] = send_values[1] = NULL;
  send_staged[0] = send_staged[1] = false;
  for (iCode *ic = chain; ic; ic = ic->next) {
    if (ic->op == RECEIVE) {
      if (ic->argreg < 1 || ic->argreg > 2) unsupported ("register receive index");
      receives[ic->argreg - 1] = ic;
    }
    if (ic->op == SEND && isOperandVolatile (ic->left, false) && register_scratch < 4) register_scratch = 4;
    if (ic->op == PCALL && register_call (ic)) register_scratch = 6;
  }
  plan_divisions (chain);
  allocate (chain);
  frame_center = choose_frame_center (chain, false);
  if (frame_center) { frame_base = true; allocate (chain); }
  function_chain = chain;
  plan_tail_arguments (chain);
  if (tail_sites) {
    allocate (chain);
    /* A larger allocation must never invalidate a site whose pushes were
       suppressed. Restore the ordinary call if its bounds no longer fit. */
    bool retry = false;
    for (cpu6_tail_site **link = &tail_sites; *link;) {
      cpu6_tail_site *site = *link;
      if (self_tail_site (site->call)) { link = &site->next; continue; }
      for (unsigned i = 0; i < site->count; i++)
        if (site->args[i].direct) site->args[i].push->generated = 0;
      *link = site->next; free (site->args); free (site); retry = true;
    }
    if (retry) allocate (chain);
  }
  if (frame_base) frame_center = choose_frame_center (chain, true);
  tail_body_label = 0;
  for (iCode *ic = chain; ic; ic = ic->next)
    if (self_tail_site (ic)) { tail_body_label = local_label++; break; }
  emit ("; CPU6 function %s begin\n", symbol_name (currFunc));
  unsigned function_asm = 0;
  for (iCode *node = chain; node; node = node->next) {
    if (node->op == INLINEASM) { function_asm = 1; break; }
    if (node->inlineAsm) function_asm = 2;
  }
  emit ("; CPU6 ABI %s frame=%d saved=%d variadic=%d asm=%u\n",
        FUNC_SDCCCALL (currFunc->type) ? "register" : "stack", frame, saved,
        IFFUNC_HASVARARGS (currFunc->type) != 0, function_asm);
  for (iCode *ic = chain; ic; ic = ic->next) {
    current_ic = ic;
    emit ("; ic %d: %u\n", ic->key, ic->op);
    if (options.iCodeInAsm) {
      const char *line = printILine (ic);
      /* The EE200 assembler has a 128-byte input buffer. */
      const char *part = line;
      while (*part) {
        unsigned count = 0;
        while (part[count] && part[count] != '\n' && count < 100) count++;
        emit ("; %.*s\n", count, part);
        part += count;
        if (*part == '\n') part++;
      }
      dbuf_free (line);
    }
    generate (ic);
  }
  emit ("; CPU6 function %s end\n", symbol_name (currFunc));
  if (!options.nopeep && !cpu6_stack_only) {
    peepHole (&genLine.lineHead);
    if (cpu6AllocateAB (genLine.lineHead)) peepHole (&genLine.lineHead);
  }
  /* Delay static-body selection until glue has resolved all data initializers
     (including function-pointer tables). The normal frontend marks references
     that survive inline expansion; raw assembly conservatively keeps bodies. */
  cpu6_function_text *text = calloc (1, sizeof (*text));
  wassert (text);
  struct dbuf_s body;
  dbuf_init (&body, 1024);
  printLine (genLine.lineHead, &body);
  text->sym = currFunc;
  text->text = dbuf_detach_c_str (&body);
  *function_text_tail = text;
  function_text_tail = &text->next;
  genLine.lineCurr = genLine.lineHead;
  while (genLine.lineCurr && genLine.lineCurr->next) genLine.lineCurr = genLine.lineCurr->next;
  destroy_line_list ();
  while (tail_sites) {
    cpu6_tail_site *next = tail_sites->next;
    free (tail_sites->args); free (tail_sites); tail_sites = next;
  }
  while (div_pairs) {
    cpu6_div_pair *next = div_pairs->next;
    free (div_pairs); div_pairs = next;
  }
}

static bool contains_symbol (const char *text, const char *name)
{
  size_t length = strlen (name);
  const char *p = text;
  while (p && (p = strstr (p, name))) {
    unsigned char before = p == text ? 0 : p[-1], after = p[length];
    if (!(isalnum (before) || before == '_' || before == '?' || before == '@') &&
        !(isalnum (after) || after == '_' || after == '?' || after == '@')) return true;
    p += length;
  }
  return false;
}

void cpu6FinishFunctions (void)
{
  /* Initializers have now been emitted, including function-pointer tables.
     Also retain raw assembly references and references from other bodies;
     retaining a dead body's dependencies is conservative but harmless. */
  for (cpu6_function_text *text = function_texts; text; text = text->next) {
    const char *name = symbol_name (text->sym);
    if (contains_symbol (dbuf_c_str (&code->oBuf), name)) text->sym->isref = 1;
    for (cpu6_function_text *other = function_texts; other; other = other->next)
      if (other != text && contains_symbol (other->text, name)) text->sym->isref = 1;
  }
  while (function_texts) {
    cpu6_function_text *text = function_texts;
    symbol *sym = text->sym;
    if (cpu6_keep_static_functions || cpu6_stack_only || inline_assembly_seen ||
        !IS_STATIC (sym->etype) || sym->isref || sym->addrtaken)
      dbuf_append_str (&code->oBuf, text->text);
    function_texts = text->next;
    dbuf_free (text->text); free (text);
  }
  function_text_tail = &function_texts;
}
