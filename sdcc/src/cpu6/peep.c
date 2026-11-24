/* CPU6 peephole dataflow. SPDX-License-Identifier: GPL-2.0-or-later */
#include "common.h"
#include "peep.h"
#include <ctype.h>

int cpu6_no_autoindex;
int cpu6_no_byte_arithmetic;
int cpu6_no_ab_allocation;

enum {
  RA = 3, RB = 12, RX = 48, RY = 192, RZ = 768, RS = 3072,
  ZF = 4096, NF = 8192, CF = 16384, OF = 32768,
  NZ = ZF | NF, FLAGS = ZF | NF | CF | OF, ALL = 65535
};

static unsigned regmask(const char *name)
{
  static const struct { const char *name; unsigned bits; } names[] = {
    {"a", RA}, {"al", 1}, {"ah", 2}, {"b", RB}, {"bl", 4}, {"bh", 8},
    {"x", RX}, {"xl", 16}, {"xh", 32}, {"y", RY}, {"yl", 64}, {"yh", 128},
    {"z", RZ}, {"zl", 256}, {"zh", 512}, {"s", RS},
    {"zf", ZF}, {"nf", NF}, {"cf", CF}, {"of", OF}, {NULL, 0}
  };
  for (unsigned n = 0; names[n].name; n++)
    if (!strcmp(name, names[n].name)) return names[n].bits;
  return 0;
}

static void decode(const char *line, char op[20], char a[256], char b[256])
{
  unsigned n = 0;
  while (isspace((unsigned char)*line)) line++;
  while (*line && !isspace((unsigned char)*line) && n < 19)
    op[n++] = tolower((unsigned char)*line++);
  op[n] = 0;
  while (isspace((unsigned char)*line)) line++;
  n = 0;
  while (*line && *line != ',' && *line != ';' && n < 255)
    a[n++] = *line++;
  while (n && isspace((unsigned char)a[n - 1])) n--;
  a[n] = 0;
  if (*line == ',') line++;
  while (isspace((unsigned char)*line)) line++;
  n = 0;
  while (*line && *line != ';' && n < 255) b[n++] = *line++;
  while (n && isspace((unsigned char)b[n - 1])) n--;
  b[n] = 0;
}

static unsigned address_reads(const char *text)
{
  unsigned mask = 0;
  while (*text) {
    if (isalnum((unsigned char)*text) || *text == '_') {
      char token[256]; unsigned n = 0;
      while (isalnum((unsigned char)*text) || *text == '_') {
        if (n < 255) token[n++] = tolower((unsigned char)*text);
        text++;
      }
      token[n] = 0;
      mask |= regmask(token);
    } else text++;
  }
  return mask;
}

static unsigned address_writes(const char *text)
{
  for (const char *reg = "abxyzs"; *reg; reg++) {
    char before[8], after[8], name[2] = {*reg, 0};
    snprintf(before, sizeof(before), "(-%c)", *reg);
    snprintf(after, sizeof(after), "(%c+)", *reg);
    if (strstr(text, before) || strstr(text, after)) return regmask(name);
  }
  return 0;
}

static unsigned branch_flag(const char *op)
{
  if (!strcmp(op, "bz") || !strcmp(op, "bnz")) return ZF;
  if (!strcmp(op, "bm") || !strcmp(op, "bp")) return NF;
  if (!strcmp(op, "bgz") || !strcmp(op, "ble")) return NF | ZF;
  if (!strcmp(op, "bl") || !strcmp(op, "bnl")) return CF;
  if (!strcmp(op, "bf") || !strcmp(op, "bnf")) return OF;
  return 0;
}

static unsigned call_arguments(lineNode *line)
{
  if (line->ic && (line->ic->op == CALL || line->ic->op == PCALL)) {
    sym_link *type = operandType(line->ic->left);
    if (IS_PTR(type)) type = type->next;
    if (IS_FUNC(type))
      return FUNC_SDCCCALL(type) == 1 && !IFFUNC_HASVARARGS(type) ? RA | RB : 0;
  }
  /* Assembly and runtime calls have no C signature to prove either scratch
     register dead. In particular CPU6_REGCALL consumes both A and B. */
  return RA | RB;
}

static unsigned byte_reg_index(const char *name)
{
  static const char *const names[16] = {
    "ah", "al", "bh", "bl", "xh", "xl", "yh", "yl",
    "zh", "zl", "sh", "sl", "ch", "cl", "ph", "pl"
  };
  for (unsigned i = 0; i < 16; i++)
    if (!strcmp(name, names[i])) return i;
  return 16;
}

static unsigned range_mask(const char *a, const char *b)
{
  unsigned r1 = byte_reg_index(a), r2 = byte_reg_index(b);
  if (r1 >= 12 || r2 >= 12) return 0;
  if (r1 > r2) { unsigned t = r1; r1 = r2; r2 = t; }
  unsigned mask = 0;
  for (unsigned r = r1; r <= r2; r++)
    mask |= (r & 1 ? 1U : 2U) << (r & ~1U);
  return mask;
}

/* Unknown instructions are barriers. Partial-register writes kill only the
   written byte. Loads, stores and transfers preserve overflow and carry. */
static bool effects(lineNode *line, unsigned *reads, unsigned *writes)
{
  char op[20], a[256], b[256];
  decode(line->line, op, a, b);
  *reads = *writes = 0;
  if (line->isComment || line->isLabel || !*op) return true;
  if (line->isInline) return false;
  unsigned dst = 0;
  if (!strcmp(op, "lda") || !strcmp(op, "sta")) dst = RA;
  if (!strcmp(op, "ldb") || !strcmp(op, "stb")) dst = RB;
  if (!strcmp(op, "ldx") || !strcmp(op, "stx")) dst = RX;
  if (!strcmp(op, "ldab") || !strcmp(op, "stab")) dst = 1;
  if (!strcmp(op, "ldbb") || !strcmp(op, "stbb")) dst = 4;
  if (dst) {
    *reads = address_reads(a);
    *writes = address_writes(a) | NZ;
    if (op[0] == 'l') *writes |= dst;
    else *reads |= dst;
    return true;
  }
  if (!strcmp(op, "ldw") || !strcmp(op, "stw")) {
    dst = regmask(a);
    if (!dst || (dst & ~(RA | RB | RX | RY | RZ | RS))) return false;
    if (op[0] == 'l') { *reads = address_reads(b); *writes = dst | NZ; }
    else { *reads = dst | address_reads(b); *writes = NZ; }
    return true;
  }
  if (!strcmp(op, "push") || !strcmp(op, "pop")) {
    unsigned mask = range_mask(a, b);
    if (!mask) return false;
    if (!strcmp(op, "push")) { *reads = mask | RS; *writes = RS; }
    else { *reads = RS; *writes = mask | RS; }
    return true;
  }
  if (!strcmp(op, "xfr") || !strcmp(op, "xfrb")) {
    if (!regmask(a) || !regmask(b)) return false;
    *reads = regmask(a); *writes = regmask(b) | NZ; return true;
  }
  if (!strcmp(op, "xab") || !strcmp(op, "xax") || !strcmp(op, "xay") || !strcmp(op, "xaz")) {
    char target[2] = {op[2], 0};
    *reads = RA; *writes = regmask(target) | NZ; return true;
  }
  if (!strcmp(op, "cla") || !strcmp(op, "clr") || !strcmp(op, "clrb")) {
    *writes = (!strcmp(op, "cla") ? RA : regmask(a)) | FLAGS;
    return (*writes & ~FLAGS) != 0;
  }
  if (!strcmp(op, "sl") || !strcmp(op, "rl")) { *writes = CF; return true; }
  if (!strcmp(op, "sf") || !strcmp(op, "rf")) { *writes = OF; return true; }
  if (!strcmp(op, "aab") || !strcmp(op, "sab") || !strcmp(op, "nab")) {
    *reads = RA | RB; *writes = RB | (!strcmp(op, "nab") ? NZ : FLAGS); return true;
  }
  if (!strcmp(op, "mul") || !strcmp(op, "div")) {
    dst = regmask(b);
    if (dst != RA && dst != RB && dst != RX && dst != RY && dst != RZ && dst != RS)
      return false; /* Explicit three-operand forms remain a dataflow barrier. */
    *reads = dst | address_reads(a);
    *writes = dst | FLAGS;
    if (dst == RA) *writes |= RB;
    if (dst == RX) *writes |= RY;
    if (dst == RZ) *writes |= RS;
    if (!strcmp(op, "div"))
      *reads |= (*writes & ~OF); /* Zero divisor preserves all but F. */
    return true;
  }
  if (!strcmp(op, "ivr") || !strcmp(op, "ivrb") || !strcmp(op, "iva")) {
    *reads = !strcmp(op, "iva") ? RA : regmask(a);
    char *end;
    long count = strtol(b, &end, 0);
    *writes = *reads | (count > 1 && !*end ? FLAGS : NZ);
    return *reads != 0;
  }
  if (!strcmp(op, "add") || !strcmp(op, "sub") || !strcmp(op, "and") ||
      !strcmp(op, "ori") || !strcmp(op, "ore")) {
    bool arith = !strcmp(op, "add") || !strcmp(op, "sub");
    char *comma = strchr(b, ',');
    if (comma) {
      char *third = comma + 1;
      while (isspace((unsigned char)*third)) third++;
      unsigned src = regmask(a), dest = regmask(third);
      if (!src || !dest) return false;
      *reads = src;
      *writes = dest | (arith ? FLAGS : NZ);
      return true;
    }
    unsigned dest = regmask(b);
    if (!dest) return false;
    *reads = (regmask(a) ? regmask(a) : address_reads(a)) | dest;
    *writes = dest | (arith ? FLAGS : NZ);
    return true;
  }
  if (!strcmp(op, "addb") || !strcmp(op, "subb") || !strcmp(op, "andb") ||
      !strcmp(op, "orib") || !strcmp(op, "oreb")) {
    if (!regmask(a) || !regmask(b)) return false;
    *reads = regmask(a) | regmask(b);
    *writes = regmask(b) | ((!strcmp(op, "addb") || !strcmp(op, "subb")) ? FLAGS : NZ);
    return true;
  }
  if (!strcmp(op, "inr") || !strcmp(op, "dcr") || !strcmp(op, "inrb") || !strcmp(op, "dcrb")) {
    if (regmask(a)) { *reads = regmask(a); *writes = *reads | NZ | OF; return true; }
    if ((!strcmp(op, "inr") || !strcmp(op, "dcr")) && strchr(a, '(')) {
      *reads = address_reads(a);
      *writes = NZ | OF;
      return true;
    }
    return false;
  }
  if (!strcmp(op, "ina") || !strcmp(op, "dca") || !strcmp(op, "inx") || !strcmp(op, "dcx")) {
    *reads = op[2] == 'x' ? RX : RA; *writes = *reads | NZ | OF; return true;
  }
  if (!strcmp(op, "slr") || !strcmp(op, "srr") || !strcmp(op, "rrr") || !strcmp(op, "rlr") ||
      !strcmp(op, "slrb") || !strcmp(op, "srrb") || !strcmp(op, "rrrb") || !strcmp(op, "rlrb")) {
    dst = regmask(a); if (!dst) return false;
    *reads = dst | (op[0] == 'r' ? CF : 0); *writes = dst | NZ | CF; return true;
  }
  if (!strcmp(op, "sla") || !strcmp(op, "sra")) {
    *reads = RA; *writes = RA | NZ | CF; return true;
  }
  if (branch_flag(op)) { *reads = branch_flag(op); return true; }
  if (!strcmp(op, "jmp") || !strcmp(op, "bra")) { *reads = address_reads(a); return true; }
  if (!strcmp(op, "jsr")) {
    *reads = RS | address_reads(a) | call_arguments(line);
    if (!strncmp(a, "__", 2)) *reads |= RB;
    if (!strncmp(a, "__cc", 4)) *reads |= FLAGS;
    *writes = RA | RB | FLAGS;
    return true;
  }
  if (!strcmp(op, "rsr")) {
    *reads = RB | RX | RY | RZ | RS; return true;
  }
  if (!strcmp(op, "nop")) return true;
  return false;
}

static bool bound_operand(const char *text)
{
  while (*text) {
    if (isalpha((unsigned char)*text)) {
      char name[3] = {*text++, 0, 0};
      if (isalpha((unsigned char)*text)) name[1] = *text++;
      unsigned mask = regmask(name);
      if (!mask || (mask & ~(RA | RB)) || isalnum((unsigned char)*text)) return false;
    } else if (isdigit((unsigned char)*text)) {
      char *end;
      strtoul(text, &end, 0);
      text = end;
    } else {
      if (!strchr(" \t+-()", *text)) return false;
      text++;
    }
  }
  return true;
}

/* Operand-bound assembly stays inside the generated function and has no
   dependencies on private symbols, position, or registers other than A/B. */
bool cpu6OperandAsm(const char *text)
{
  char *copy = Safe_strdup(text);
  bool valid = true;
  for (char *line = copy; line && valid; ) {
    char *end = strchr(line, '\n');
    if (end) *end++ = 0;
    char op[20], a[256], b[256];
    decode(line, op, a, b);
    if (*op && *op != ';') {
      lineNode node = {0};
      node.line = line;
      unsigned reads, writes;
      valid = strlen(line) < 127 && !branch_flag(op) && strcmp(op, "jmp") &&
        strcmp(op, "bra") && strcmp(op, "jsr") && strcmp(op, "rsr") &&
        bound_operand(a) && bound_operand(b) && effects(&node, &reads, &writes) &&
        !((reads | writes) & ~(RA | RB | FLAGS));
    }
    line = end;
  }
  Safe_free(copy);
  return valid;
}

static lineNode *find_label(const char *label, lineNode *head)
{
  size_t length = strlen(label);
  for (lineNode *line = head; line; line = line->next)
    if (line->isLabel && !strncmp(line->line, label, length) && line->line[length] == ':')
      return line;
  return NULL;
}

static bool unused_path(unsigned bit, lineNode *line, lineNode *head)
{
  for (; line; line = line->next) {
    if (line->visited) return true;
    line->visited = 1;
    unsigned reads, writes;
    if (!effects(line, &reads, &writes) || (reads & bit)) return false;
    if (writes & bit) return true;
    if (line->isComment || line->isLabel) continue;
    char op[20], a[256], b[256];
    decode(line->line, op, a, b);
    if (!strcmp(op, "rsr")) return true;
    if (branch_flag(op) || !strcmp(op, "jmp") || !strcmp(op, "bra")) {
      lineNode *target = find_label(a, head);
      /* Generated external jumps are tail calls. C callees receive arguments
         on S, the return link in X, and preserve Y/Z. Runtime register-entry
         helpers (double underscore) remain conservative barriers. */
      if (!target && !strcmp(op, "jmp") && a[0] == '_' && a[1] != '_')
        return !(bit & (RX | RY | RZ | RS | call_arguments(line)));
      if (!target || !unused_path(bit, target, head)) return false;
      if (!branch_flag(op)) return true;
    }
  }
  return true;
}

bool cpu6notUsed(const char *what, lineNode *end, lineNode *head)
{
  unsigned mask = regmask(what);
  if (!mask || !end) return false;
  for (unsigned bit = 1; bit <= OF; bit <<= 1) {
    if (!(mask & bit)) continue;
    for (lineNode *line = head; line; line = line->next) line->visited = 0;
    if (!unused_path(bit, end->next, head)) return false;
  }
  return true;
}

bool cpu6notUsedFrom(const char *what, const char *label, lineNode *head)
{
  lineNode *start = find_label(label, head);
  return start && cpu6notUsed(what, start, head);
}

/* Late allocation sees the actual implicit A/B uses, including byte halves,
   helper calls and address generation. Recolor a complete local live range
   from X/Y/Z to its incoming A/B register only if it has no interference.
   The CFG liveness query proves the old register dead at the end. Labels,
   calls and unknown instructions bound regions; no ABI saves are removed. */
static bool ab_barrier(lineNode *line, const char *op, const char *a)
{
  if (line->isLabel || line->isInline || branch_flag(op) ||
      !strcmp(op, "jmp") || !strcmp(op, "bra") || !strcmp(op, "jsr") ||
      !strcmp(op, "rsr") || !strcmp(op, "mul") || !strcmp(op, "div") ||
      !strcmp(op, "push") || !strcmp(op, "pop"))
    return true;
  if ((!strcmp(op, "inr") || !strcmp(op, "dcr") || !strcmp(op, "clr") ||
       !strcmp(op, "ivr") || !strcmp(op, "slr") || !strcmp(op, "srr")) &&
      strchr(a, '('))
    return true;
  return false;
}

static void rename_register(lineNode *line, char from, char to)
{
  char op[20], a[256], b[256], buffer[600];
  decode(line->line, op, a, b);
  if ((!strcmp(op, "ldx") || !strcmp(op, "stx")) && from == 'x') op[2] = to;
  else if ((!strcmp(op, "inx") || !strcmp(op, "dcx")) && from == 'x') {
    strcpy(op, op[0] == 'i' ? "inr" : "dcr");
    a[0] = to; a[1] = 0;
  } else if (op[0] == 'x' && op[1] == 'a' && op[2] == from && !op[3]) {
    strcpy(op, "xfr"); strcpy(a, "a"); b[0] = to; b[1] = 0;
  }
  char *operands[] = {a, b};
  for (unsigned i = 0; i < 2; i++) {
    char *p = operands[i];
    while (*p) {
      if (isalnum((unsigned char)*p) || *p == '_') {
        char *start = p;
        while (isalnum((unsigned char)*p) || *p == '_') p++;
        if (*start == from && (p == start + 1 ||
            (p == start + 2 && (start[1] == 'l' || start[1] == 'h')))) *start = to;
      } else p++;
    }
  }
  snprintf(buffer, sizeof(buffer), "%s%s%s%s%s", op, *a ? " " : "", a, *b ? "," : "", b);
  Safe_free(line->line);
  line->line = Safe_strdup(buffer);
  if (line->aln) Safe_free(line->aln);
  line->aln = NULL;
}

bool cpu6AllocateAB(lineNode *head)
{
  if (cpu6_no_ab_allocation) return false;
  bool changed = false;
  for (lineNode *start = head; start; start = start->next) {
    char op[20], source[256], target[256];
    decode(start->line, op, source, target);
    if (start->isInline || strcmp(op, "xfr") || strlen(source) != 1 ||
        !strchr("ab", source[0]) || strlen(target) != 1 || !strchr("xyz", target[0])) continue;
    unsigned old = regmask(target);
    for (unsigned choice = 0; choice < 2; choice++) {
      char destination[2] = {choice ? (source[0] == 'a' ? 'b' : 'a') : source[0], 0};
      unsigned candidate = regmask(destination);
      if (choice && !cpu6notUsed(destination, start, head)) continue;
      lineNode *end = NULL;
      unsigned count = 0;
      for (lineNode *line = start->next; line && count < 160; line = line->next) {
        if (line->isComment) continue;
        count++;
        char insn[20], a[256], b[256]; unsigned reads, writes;
        decode(line->line, insn, a, b);
        if (ab_barrier(line, insn, a) || !effects(line, &reads, &writes)) break;
        bool last = (reads & old) && !(writes & old) && cpu6notUsed(target, line, head);
        /* A final copy back, or an address load into the candidate itself,
           may terminate the range. Its old candidate value is never read. */
        bool coalesced = last && (writes & candidate) == candidate && !(reads & candidate);
        if ((reads | writes) & candidate) {
          if (coalesced) end = line;
          break;
        }
        if ((writes & old) && !(reads & old)) break;
        if (last && cpu6notUsed(destination, line, head)) { end = line; break; }
      }
      if (!end) continue;
      for (lineNode *line = start; ; line = line->next) {
        if (!line->isComment) rename_register(line, target[0], destination[0]);
        if (line == end) break;
      }
      changed = true;
      break;
    }
  }
  return changed;
}

static bool word_register(const char *name)
{
  unsigned mask = regmask(name);
  return mask == RA || mask == RB || mask == RX || mask == RY || mask == RZ;
}

/* Ordinary A/B loads and stores encode (register) in one byte. */
static bool compact_word_address(const char *src)
{
  const char *paren = strchr(src, '(');
  if (!paren || !paren[1] || !strchr("abxyzs", paren[1]) ||
      paren[2] != ')' || paren[3]) return false;
  if (src == paren) return true;
  char *end;
  return strtol(src, &end, 0) == 0 && end == paren;
}

bool cpu6canAssign(const char *dst, const char *src, const char *kind)
{
  if (kind && !strcmp(kind, "byte-arithmetic"))
    return !cpu6_no_byte_arithmetic && !strcmp(dst, "bl") && !strcmp(src, "al");
  if (kind && !strncmp(kind, "autoindex-", 10)) {
    if (cpu6_no_autoindex) return false;
    if (!strcmp(kind, "autoindex-base")) return word_register(src);
    if (!strcmp(kind, "autoindex-offset") || !strcmp(kind, "autoindex-spill")) {
      if (!word_register(dst)) return false;
      char *end;
      long offset = strtol(src, &end, 0);
      if (offset < -128 || offset > 127) return false;
      if (!strcmp(kind, "autoindex-spill"))
        return !strcmp(end, "(s)");
      return end != src && !*end;
    }
    if (!strcmp(kind, "autoindex-spill-op"))
      return (!strcmp(dst, "lda") && !strcmp(src, "sta")) ||
             (!strcmp(dst, "ldb") && !strcmp(src, "stb")) ||
             (!strcmp(dst, "ldx") && !strcmp(src, "stx")) ||
             (!strcmp(dst, "ldab") && !strcmp(src, "stab")) ||
             (!strcmp(dst, "ldbb") && !strcmp(src, "stbb"));
    unsigned value = 0, size = 0;
    if (!strcmp(dst, "lda") || !strcmp(dst, "sta")) { value = RA; size = 2; }
    if (!strcmp(dst, "ldb") || !strcmp(dst, "stb")) { value = RB; size = 2; }
    if (!strcmp(dst, "ldx") || !strcmp(dst, "stx")) { value = RX; size = 2; }
    if (!strcmp(dst, "ldab") || !strcmp(dst, "stab")) { value = 1; size = 1; }
    if (!strcmp(dst, "ldbb") || !strcmp(dst, "stbb")) { value = 4; size = 1; }
    unsigned wanted = !strcmp(kind, "autoindex-byte") ? 1 :
                      !strcmp(kind, "autoindex-word") ? 2 :
                      !strcmp(kind, "autoindex-any") ? size : 0;
    /* Restrict C peepholes to A/B/X/Y/Z and exclude every byte alias.
       S, C and P require separate stack/context/control-flow reasoning. */
    return wanted && size == wanted && word_register(src) && !(regmask(src) & value);
  }
  if (!word_register(dst)) return false;
  if (!kind) return word_register(src);
  if (!strcmp(kind, "alu-literal-or-direct")) {
    if (!*src || strchr(src, '@') || strchr(src, ',') || regmask(src)) return false;
    if (!strchr(src, '(')) return true;
    return src[0] == '(' && src[1] == '_' && src[strlen(src)-1] == ')' &&
           !address_reads(src);
  }
  if (!strcmp(kind, "pointer-cell"))
    return !strchr(src, '@') && !address_writes(src) && strchr(src, '(') &&
           (address_reads(src) || strstr(src, "(_"));
  if (!strcmp(kind, "signed-byte-constant")) {
    char *end;
    long value = strtol(src, &end, 0);
    return end != src && !*end && ((value >= -128 && value <= 127) ||
                                   (value >= 0xff80 && value <= 0xffff));
  }
  if (!strcmp(kind, "independent-address"))
    return !(address_reads(src) & regmask(dst)) && !address_writes(src);
  if (!strcmp(kind, "stable-load"))
    return !address_writes(src) && !(src[0] == '(' && isdigit((unsigned char)src[1]));
  if (!strcmp(kind, "stable-memory"))
    return strchr(src, '(') && strchr(src, ')') && !address_writes(src) &&
           (address_reads(src) || strstr(src, "(_"));
  /* A compact load/store plus its transfer or ALU operation totals two or
     three bytes. The extended indexed form always takes four. */
  if (optimize.codeSize && (!strcmp(kind, "extended-load") || !strcmp(kind, "extended-store") ||
                            !strcmp(kind, "alu-memory")) && compact_word_address(src))
    return false;
  if (!strcmp(kind, "extended-load"))
    return !address_writes(src) && !strchr(src, '@') && !regmask(src) &&
           !(src[0] == '(' && isdigit((unsigned char)src[1]));
  if (!strcmp(kind, "extended-store"))
    return strchr(src, '(') && strchr(src, ')') && !address_writes(src) &&
           !strchr(src, '@') && !(address_reads(src) & regmask(dst));
  if (!strcmp(kind, "alu-memory"))
    return strchr(src, '(') && strchr(src, ')') && !address_writes(src) &&
           !strchr(src, '@') && !(address_reads(src) & regmask(dst)) &&
           (address_reads(src) || strstr(src, "(_"));
  if (!strcmp(kind, "rmw-memory"))
    return strchr(src, '(') && strchr(src, ')') && !address_writes(src) &&
           !strchr(src, '@') && !(address_reads(src) & (RA | regmask(dst))) &&
           (address_reads(src) || strstr(src, "(_"));
  if (!strcmp(kind, "small-const")) {
    char *end;
    long v = strtol(src, &end, 0);
    return end != src && !*end && v >= 0 && v <= 15;
  }
  if (!strcmp(kind, "immediate-value"))
    return !strchr(src, '(') && !strchr(src, ')') && !strchr(src, '@') && !regmask(src);
  return false;
}

int cpu6instructionSize(lineNode *line)
{
  if (line->isComment || line->isLabel || !*line->line) return 0;
  if (line->isInline) {
    if (!line->ic || line->ic->op != CALL || !line->ic->inlineAsm) return 999;
    /* Operand-bound assembly was validated by cpu6OperandAsm. Keep the
       optimization barrier, but use the encoded size for branch relaxation. */
    lineNode instruction = *line;
    instruction.isInline = false;
    return cpu6instructionSize(&instruction);
  }
  char op[20], a[256], b[256]; unsigned reads, writes;
  decode(line->line, op, a, b);
  if (!strcmp(op, ".word") && !*b) return 2; /* one jump-table entry */
  if (!strcmp(op, "cpy")) return 1;
  if ((!strcmp(op, "addb") || !strcmp(op, "subb") || !strcmp(op, "andb")) &&
      !strcmp(a, "al") && !strcmp(b, "bl")) return 1;
  if (!strcmp(op, "ldw") || !strcmp(op, "stw")) return 4;
  if (!strcmp(op, "push") || !strcmp(op, "pop")) return 2;
  if (!strcmp(op, "add") || !strcmp(op, "sub") || !strcmp(op, "and") ||
      !strcmp(op, "ori") || !strcmp(op, "ore") || !strcmp(op, "mul") || !strcmp(op, "div")) {
    /* Peephole names such as "cf" can be ordinary assembler symbols. */
    unsigned registers = RA | RB | RX | RY | RZ | RS;
    return (regmask(a) & registers) && (regmask(b) & registers) ? 2 : 4;
  }
  if ((!strcmp(op, "inr") || !strcmp(op, "dcr")) && strchr(a, '(')) return 4;
  /* Relaxable conditional jumps expand to a branch over a three-byte JMP. */
  if (op[0] == 'j' && strcmp(op, "jmp") && strcmp(op, "jsr")) return 5;
  if (!strcmp(op, "bra") || !strcmp(op, "bsr")) return 3; /* May relax to two. */
  if (!effects(line, &reads, &writes)) return 999;
  if (branch_flag(op)) return 2;
  bool jump = !strcmp(op, "jmp") || !strcmp(op, "jsr");
  if (jump || !strncmp(op, "ld", 2) || !strncmp(op, "st", 2)) {
    bool indirect = a[0] == '@';
    const char *addr = indirect ? a + 1 : a;
    const char *paren = strchr(addr, '(');
    if (!paren) return !strcmp(op, "ldab") || !strcmp(op, "ldbb") ? 2 : 3;
    /* Autoindex encodes an explicit zero displacement, ordinary indexing
       elides it. Jumps, indirect loads and X loads use an index byte. */
    if (address_writes(addr)) return paren == addr ? 2 : 3;
    if (compact_word_address(addr))
      return jump || indirect || !strcmp(op, "ldx") || !strcmp(op, "stx") ? 2 : 1;
    return 3;
  }
  if (!strcmp(op, "xfr") && !strcmp(a, "a") && word_register(b) && strcmp(b, "a"))
    return 1;
  if ((!strcmp(op, "inr") || !strcmp(op, "dcr") || !strcmp(op, "clr") ||
       !strcmp(op, "slr") || !strcmp(op, "srr")) && !strcmp(a, "a") && !*b) return 1;
  if (!strcmp(op, "aab") || !strcmp(op, "sab") || !strcmp(op, "nab") ||
      !strcmp(op, "xab") || !strcmp(op, "xax") || !strcmp(op, "xay") ||
      !strcmp(op, "xaz") || !strcmp(op, "cla") || !strcmp(op, "iva") || !strcmp(op, "rsr") ||
      !strcmp(op, "rl") || !strcmp(op, "sl") || !strcmp(op, "rf") ||
      !strcmp(op, "sf") || !strcmp(op, "nop")) return 1;
  return 2;
}

/* Loop rotation, backedge flag reuse and single-block constant hoisting. */
static const char *invert_branch(const char *op)
{
  if (!strcmp(op, "bz")) return "bnz";
  if (!strcmp(op, "bnz")) return "bz";
  if (!strcmp(op, "bm")) return "bp";
  if (!strcmp(op, "bp")) return "bm";
  if (!strcmp(op, "bgz")) return "ble";
  if (!strcmp(op, "ble")) return "bgz";
  if (!strcmp(op, "bl")) return "bnl";
  if (!strcmp(op, "bnl")) return "bl";
  if (!strcmp(op, "bf")) return "bnf";
  if (!strcmp(op, "bnf")) return "bf";
  return NULL;
}

static lineNode *next_real(lineNode *line)
{
  while (line && line->isComment) line = line->next;
  return line;
}

static lineNode *prev_real(lineNode *line)
{
  while (line && line->isComment) line = line->prev;
  return line;
}

static bool label_name(lineNode *line, char out[256])
{
  if (!line || !line->isLabel || !line->line) return false;
  const char *p = line->line;
  while (isspace((unsigned char)*p)) p++;
  unsigned n = 0;
  while (*p && *p != ':' && !isspace((unsigned char)*p) && n < 255) out[n++] = *p++;
  out[n] = 0;
  return n > 0 && *p == ':';
}

static unsigned count_label_refs(lineNode *head, const char *name)
{
  unsigned count = 0;
  for (lineNode *line = head; line; line = line->next) {
    if (line->isComment || line->isLabel) continue;
    char op[20], a[256], b[256];
    decode(line->line, op, a, b);
    if ((branch_flag(op) || !strcmp(op, "jmp") || !strcmp(op, "bra") ||
         !strcmp(op, "jsr") || !strcmp(op, ".word")) && !strcmp(a, name))
      count++;
    else if (strstr(a, name) || strstr(b, name))
      count++;
  }
  return count;
}

static int span_bytes(lineNode *from, lineNode *to)
{
  int total = 0;
  for (lineNode *line = from; line && line != to; line = line->next) {
    int sz = cpu6instructionSize(line);
    if (sz > 127) return 999;
    total += sz;
    if (total > 127) return 999;
  }
  return total;
}

static lineNode *insert_after(lineNode *pos, const char *text, bool is_label)
{
  lineNode *node = newLineNode(text);
  node->isLabel = is_label;
  node->ic = pos->ic;
  node->prev = pos;
  node->next = pos->next;
  if (pos->next) pos->next->prev = node;
  pos->next = node;
  return node;
}

static void replace_line(lineNode *line, const char *text)
{
  Safe_free(line->line);
  line->line = Safe_strdup(text);
  if (line->aln) { Safe_free(line->aln); line->aln = NULL; }
}

static void move_before(lineNode *node, lineNode *target)
{
  if (!node || !target || node == target || node->next == target || !node->prev || !target->prev)
    return;
  node->prev->next = node->next;
  if (node->next) node->next->prev = node->prev;
  node->prev = target->prev;
  node->next = target;
  target->prev->next = node;
  target->prev = node;
}

static bool label_follows(lineNode *line, const char *target_name)
{
  for (lineNode *p = line->next; p; p = p->next) {
    if (p->isComment) continue;
    if (!p->isLabel) return false;
    char name[256];
    if (label_name(p, name) && !strcmp(name, target_name)) return true;
  }
  return false;
}

static bool is_pure_header_insn(lineNode *line)
{
  if (!line || line->isComment || line->isLabel || line->isInline || line->mightBeVolatileAccess)
    return false;
  char op[20], a[256], b[256];
  unsigned reads, writes;
  decode(line->line, op, a, b);
  if (!effects(line, &reads, &writes)) return false;
  if (writes & RS) return false;
  if (address_writes(a) || address_writes(b)) return false;
  return !strcmp(op, "lda") || !strcmp(op, "ldb") || !strcmp(op, "ldx") || !strcmp(op, "ldw") ||
         !strcmp(op, "ldab") || !strcmp(op, "ldbb") ||
         !strcmp(op, "xfr") || !strcmp(op, "xfrb") || !strcmp(op, "xab") ||
         !strcmp(op, "xax") || !strcmp(op, "xay") || !strcmp(op, "xaz") ||
         !strcmp(op, "add") || !strcmp(op, "sub") || !strcmp(op, "and") ||
         !strcmp(op, "ori") || !strcmp(op, "ore") ||
         !strcmp(op, "aab") || !strcmp(op, "sab") || !strcmp(op, "nab") ||
         !strcmp(op, "addb") || !strcmp(op, "subb") || !strcmp(op, "andb") ||
         !strcmp(op, "orib") || !strcmp(op, "oreb") ||
         !strcmp(op, "clrb") || !strcmp(op, "clr") || !strcmp(op, "cla");
}

static bool sets_zf_for_reg(lineNode *line, char reg)
{
  if (!line || line->isComment || line->isLabel || line->isInline) return false;
  char op[20], a[256], b[256];
  decode(line->line, op, a, b);
  if ((!strcmp(op, "dcr") || !strcmp(op, "inr")) && a[0] == reg && !a[1]) return true;
  if ((!strcmp(op, "dcx") || !strcmp(op, "inx")) && reg == 'x') return true;
  if ((!strcmp(op, "dca") || !strcmp(op, "ina")) && reg == 'a') return true;
  return false;
}

static bool is_const_load(lineNode *line, unsigned *dst_out)
{
  if (!line || line->isComment || line->isLabel || line->isInline || line->mightBeVolatileAccess)
    return false;
  char op[20], a[256], b[256];
  unsigned reads, writes;
  decode(line->line, op, a, b);
  if (!effects(line, &reads, &writes) || reads) return false;
  if (!strcmp(op, "cla") || !strcmp(op, "clr") || !strcmp(op, "clrb")) {
    *dst_out = writes & ~FLAGS;
    return *dst_out != 0;
  }
  if ((!strcmp(op, "ldbb") || !strcmp(op, "ldab") || !strcmp(op, "ldb") ||
       !strcmp(op, "lda") || !strcmp(op, "ldx")) &&
      !strchr(a, '(') && !regmask(a)) {
    *dst_out = writes & ~FLAGS;
    return *dst_out != 0;
  }
  return false;
}

static bool flags_dead_after(lineNode *line, lineNode *head, unsigned writes)
{
  if ((writes & ZF) && !cpu6notUsed("zf", line, head)) return false;
  if ((writes & NF) && !cpu6notUsed("nf", line, head)) return false;
  if ((writes & CF) && !cpu6notUsed("cf", line, head)) return false;
  if ((writes & OF) && !cpu6notUsed("of", line, head)) return false;
  return true;
}

/* The compiler spells a rematerialized static address as symbol+offset.
   Keep the whole offset in the object, without wrapping the length. */
static bool static_offset(const char *address, char symbol[256], unsigned *offset)
{
  unsigned n = 0;
  if (*address != '_') return false;
  while (isalnum((unsigned char)address[n]) || address[n] == '_') n++;
  if (n >= 256 || address[n] != '+' || !isdigit((unsigned char)address[n + 1])) return false;
  char *end;
  unsigned long value = strtoul(address + n + 1, &end, 10);
  if (*end || value > 65535) return false;
  memcpy(symbol, address, n); symbol[n] = 0; *offset = (unsigned)value;
  return true;
}

static bool outside_entry(lineNode *head, lineNode *label, lineNode *back)
{
  char name[256];
  if (!label_name(label, name) || name[0] != 'L' || !isdigit((unsigned char)name[1])) return true;
  size_t size = strlen(name);
  for (lineNode *p = head; p; p = p->next) {
    if (p == back || p->isComment || p->isLabel) continue;
    if (p->isInline) return true;
    for (const char *s = p->line; (s = strstr(s, name)); s += size)
      if ((s == p->line || !(isalnum((unsigned char)s[-1]) || s[-1] == '_')) &&
          !(isalnum((unsigned char)s[size]) || s[size] == '_')) return true;
  }
  return false;
}

/* Replace a single-entry byte-fill loop with a forward overlapping CPY.
   Store one seed byte and copy each byte onto its successor. CPY encodes a
   count minus one. The six replacement instructions occupy 14 bytes. */
static bool block_fill(lineNode *head, lineNode *label, lineNode *compare,
                       lineNode *exit, lineNode *back)
{
  char op[20], a[256], b[256], start[256], limit[256], addr[256], ptr[2] = {0};
  unsigned first, last;
  decode(exit->line, op, a, b);
  if (strcmp(op, "bz")) return false;
  lineNode *init = prev_real(label->prev);
  while (init && init->isLabel) init = prev_real(init->prev);
  if (!init) return false;
  decode(init->line, op, a, b);
  if (!strcmp(op, "ldx")) { ptr[0] = 'x'; strcpy(addr, a); }
  else if (!strcmp(op, "ldw") && (!strcmp(a, "y") || !strcmp(a, "z"))) {
    ptr[0] = a[0]; strcpy(addr, b);
  } else return false;
  if (!static_offset(addr, start, &first)) return false;
  decode(compare->line, op, a, b);
  char *dest = strrchr(b, ',');
  if (strcmp(op, "sub") || strcmp(a, ptr) || !dest || strcmp(dest, ",b")) return false;
  *dest = 0;
  if (!static_offset(b, limit, &last) || strcmp(start, limit) || last < first + 2 ||
      !cpu6FillArray(compare->ic, start, last)) return false;
  lineNode *value = next_real(exit->next);
  while (value && value->isLabel) value = next_real(value->next);
  if (!value) return false;
  decode(value->line, op, a, b);
  if (strcmp(op, "ldbb") || !isdigit((unsigned char)*a) || *b) return false;
  char *end;
  unsigned long byte = strtoul(a, &end, 0);
  if (*end || byte > 255) return false;
  lineNode *store = next_real(value->next);
  if (!store || next_real(store->next) != back) return false;
  decode(store->line, op, a, b);
  char index[8];
  snprintf(index, sizeof(index), "(%c+)", ptr[0]);
  if (strcmp(op, "stbb") || strcmp(a, index)) return false;
  for (lineNode *p = init; p != back; p = p->next)
    if (p->isInline || p->mightBeVolatileAccess || (p->isLabel && outside_entry(head, p, back)))
      return false;
  if (!flags_dead_after(back, head, FLAGS) || !cpu6notUsed("a", back, head) ||
      !cpu6notUsed("b", back, head) || !cpu6notUsed("y", back, head) ||
      !cpu6notUsed(ptr, back, head)) return false;
  char text[320];
  snprintf(text, sizeof(text), "ldb %s", addr); replace_line(init, text);
  snprintf(text, sizeof(text), "ldab %lu", byte); replace_line(compare, text);
  replace_line(exit, "stab (b)");
  snprintf(text, sizeof(text), "ldw y,%s+%u", start, first + 1); replace_line(value, text);
  snprintf(text, sizeof(text), "lda %u", last - first - 2); replace_line(store, text);
  replace_line(back, "cpy");
  return true;
}

static bool hoist_single_block_loop(lineNode *head, lineNode *rot_lbl, lineNode *back_br)
{
  char rname[256];
  if (!label_name(rot_lbl, rname) || count_label_refs(head, rname) != 1) return false;
  lineNode *before = prev_real(rot_lbl->prev);
  if (!before) return false;
  char bop[20], ba[256], bb[256];
  decode(before->line, bop, ba, bb);
  if (!strcmp(bop, "jmp") || !strcmp(bop, "bra") || !strcmp(bop, "rsr")) return false;

  unsigned loop_reads = 0, loop_writes = 0;
  for (lineNode *p = rot_lbl->next; p && p != back_br; p = p->next) {
    if (p->isComment) continue;
    if (p->isLabel) {
      char lname[256];
      if (!label_name(p, lname) || count_label_refs(head, lname) != 0) return false;
      continue;
    }
    if (p->isInline) return false;
    char op[20], a[256], b[256];
    unsigned r, w;
    decode(p->line, op, a, b);
    if (branch_flag(op) || !strcmp(op, "jmp") || !strcmp(op, "bra") ||
        !strcmp(op, "jsr") || !strcmp(op, "rsr") || !effects(p, &r, &w))
      return false;
    loop_reads |= r & ~FLAGS;
    loop_writes |= w & ~FLAGS;
  }

  bool changed = false;
  /* If B is clobbered elsewhere in the loop (e.g., comparison) while A is
     completely free in and after the loop, retarget a byte-constant store to A
     so the constant load becomes hoistable. */
  if ((loop_writes & RB) && !((loop_reads | loop_writes) & RA) &&
      cpu6notUsed("a", back_br, head)) {
    for (lineNode *p = rot_lbl->next; p && p != back_br; p = p->next) {
      if (p->isComment || p->isLabel) continue;
      char op[20], a[256], b[256];
      decode(p->line, op, a, b);
      if (strcmp(op, "ldbb") || strchr(a, '(') || regmask(a)) continue;
      lineNode *q = next_real(p->next);
      if (!q || q == back_br || q->isLabel) continue;
      char op2[20], a2[256], b2[256];
      decode(q->line, op2, a2, b2);
      if (strcmp(op2, "stbb") || (address_reads(a2) & (RA | RB)) ||
          (address_writes(a2) & (RA | RB)))
        continue;
      if (!cpu6notUsed("bl", q, head)) continue;
      char buf[300];
      snprintf(buf, sizeof(buf), "ldab %s", a);
      replace_line(p, buf);
      snprintf(buf, sizeof(buf), "stab %s", a2);
      replace_line(q, buf);
      changed = true;
      break;
    }
  }

  /* Hoist loop-invariant constant loads immediately before rot_lbl. */
  bool progress = true;
  while (progress) {
    progress = false;
    unsigned prior_reads = 0;
    for (lineNode *p = rot_lbl->next; p && p != back_br; p = p->next) {
      if (p->isComment || p->isLabel) continue;
      unsigned r, w, dst;
      if (!effects(p, &r, &w)) break;
      if (is_const_load(p, &dst) && !(prior_reads & (dst | (w & FLAGS))) && flags_dead_after(p, head, w)) {
        unsigned other_writes = 0;
        for (lineNode *q = rot_lbl->next; q && q != back_br; q = q->next) {
          if (q == p || q->isComment || q->isLabel) continue;
          unsigned qr, qw;
          if (effects(q, &qr, &qw)) other_writes |= qw & ~FLAGS;
        }
        if (!(other_writes & dst)) {
          move_before(p, rot_lbl);
          changed = progress = true;
          break;
        }
      }
      prior_reads |= r;
    }
  }
  return changed;
}

bool cpu6OptimizeLoops(lineNode *head)
{
  static unsigned rot_id = 9000000;
  bool changed = false;

  for (lineNode *line = head; line; line = line->next) {
    char hname[256];
    if (!label_name(line, hname)) continue;

    /* Match header: 1-2 pure test instructions followed by conditional exit. */
    lineNode *h1 = next_real(line->next);
    if (!h1 || h1->isLabel) continue;
    lineNode *h2 = NULL, *exit_br = NULL;
    char eop[20], ea[256], eb[256];

    lineNode *after_h1 = next_real(h1->next);
    if (!after_h1 || after_h1->isLabel) continue;
    decode(after_h1->line, eop, ea, eb);
    if (invert_branch(eop)) {
      exit_br = after_h1;
    } else if (!optimize.codeSize && is_pure_header_insn(h1) && is_pure_header_insn(after_h1)) {
      h2 = after_h1;
      lineNode *after_h2 = next_real(h2->next);
      if (after_h2 && !after_h2->isLabel) {
        decode(after_h2->line, eop, ea, eb);
        if (invert_branch(eop)) exit_br = after_h2;
      }
    }
    if (!exit_br || exit_br->isInline || !is_pure_header_insn(h1)) continue;

    const char *inv = invert_branch(eop);
    if (!inv) continue;

    /* Find the matching backedge bra/jmp hname whose exit label immediately follows. */
    lineNode *back_br = NULL;
    for (lineNode *p = exit_br->next; p; p = p->next) {
      if (p->isComment || p->isLabel) continue;
      char pop[20], pa[256], pb[256];
      decode(p->line, pop, pa, pb);
      if ((!strcmp(pop, "bra") || !strcmp(pop, "jmp")) && !strcmp(pa, hname) &&
          label_follows(p, ea)) {
        back_br = p;
        break;
      }
    }
    if (!back_br || back_br->isInline) continue;

    if (!h2 && block_fill(head, line, h1, exit_br, back_br)) {
      changed = true;
      continue;
    }
    /* Case 1: Countdown/countup flag reuse (xfr R,b or ori R,R; bz/bnz Lexit; ...; dcr/inr R; bra Lhead). */
    char test_reg = 0;
    if (!h2 && (!strcmp(eop, "bz") || !strcmp(eop, "bnz"))) {
      char hop[20], ha[256], hb[256];
      decode(h1->line, hop, ha, hb);
      if (!strcmp(hop, "xfr") && !strcmp(hb, "b") && strlen(ha) == 1 && strchr("xyz", ha[0]) &&
          cpu6notUsed("b", h1, head))
        test_reg = ha[0];
      else if (!strcmp(hop, "ori") && strlen(ha) == 1 && !strcmp(ha, hb) && strchr("abxyz", ha[0]))
        test_reg = ha[0];
    }

    lineNode *upd = prev_real(back_br->prev);
    if (test_reg && upd && !upd->isLabel && sets_zf_for_reg(upd, test_reg) &&
        span_bytes(exit_br->next, back_br) <= 116) {
      char lbl_def[32], lbl_use[32], br_text[64];
      unsigned id = rot_id++;
      snprintf(lbl_def, sizeof(lbl_def), "L%u:", id);
      snprintf(lbl_use, sizeof(lbl_use), "L%u", id);
      lineNode *rot_lbl = insert_after(exit_br, lbl_def, true);
      snprintf(br_text, sizeof(br_text), "%s %s", inv, lbl_use);
      replace_line(back_br, br_text);
      hoist_single_block_loop(head, rot_lbl, back_br);
      changed = true;
      continue;
    }

    /* Case 2: General small-header loop rotation (speed mode). */
    if (!optimize.codeSize) {
      int hdr_sz = cpu6instructionSize(h1) + (h2 ? cpu6instructionSize(h2) : 0);
      if (hdr_sz <= 8 && span_bytes(exit_br->next, back_br) + hdr_sz <= 110) {
        char lbl_def[32], lbl_use[32], br_text[64];
        unsigned id = rot_id++;
        snprintf(lbl_def, sizeof(lbl_def), "L%u:", id);
        snprintf(lbl_use, sizeof(lbl_use), "L%u", id);
        lineNode *rot_lbl = insert_after(exit_br, lbl_def, true);
        lineNode *pos = back_br->prev;
        pos = insert_after(pos, h1->line, false);
        if (h2) pos = insert_after(pos, h2->line, false);
        snprintf(br_text, sizeof(br_text), "%s %s", inv, lbl_use);
        replace_line(back_br, br_text);
        hoist_single_block_loop(head, rot_lbl, back_br);
        changed = true;
      }
    }
  }
  return changed;
}

/* Earlier rewrites can grow a span after a short conditional was selected.
   Keep the raw opcode when it fits even if every intervening conditional
   expands. Otherwise let the assembler select the encoding using its final layout. */
static bool short_branch_reaches(lineNode *branch, const char *target, bool backward)
{
  int remaining = backward ? 126 : 127; /* Relative to the following PC. */
  for (lineNode *p = backward ? branch->prev : branch->next; p && remaining >= 0;
       p = backward ? p->prev : p->next) {
    if (p->isComment) continue;
    if (p->isLabel) {
      char label[256];
      if (label_name(p, label) && !strcmp(target, label)) return true;
      continue;
    }
    char op[20], a[256], b[256];
    decode(p->line, op, a, b);
    int size = cpu6instructionSize(p);
    if (!p->isInline && branch_flag(op)) size = 5;
    remaining -= size;
  }
  return false;
}

void cpu6FinalizeBranches(lineNode *head)
{
  /* Assembler mnemonics correspond to opcodes 0x10 through 0x19. */
  static const struct { const char *op, *relaxable; } forms[] = {
    {"bl", "jc"}, {"bnl", "jcc"}, {"bf", "jn"}, {"bnf", "jnc"},
    {"bz", "jz"}, {"bnz", "jnz"}, {"bm", "jlt"}, {"bp", "jge"},
    {"bgz", "jle"}, {"ble", "jgt"},
  };
  for (lineNode *p = head; p; p = p->next) {
    if (p->isInline || p->isLabel || p->isComment) continue;
    char op[20], target[256], unused[256];
    decode(p->line, op, target, unused);
    if (!branch_flag(op) || short_branch_reaches(p, target, false) ||
        short_branch_reaches(p, target, true)) continue;
    for (unsigned n = 0; n < sizeof(forms)/sizeof(forms[0]); n++) {
      if (!strcmp(op, forms[n].op)) {
        char text[280];
        snprintf(text, sizeof(text), "%s %s", forms[n].relaxable, target);
        replace_line(p, text);
        break;
      }
    }
  }
}
