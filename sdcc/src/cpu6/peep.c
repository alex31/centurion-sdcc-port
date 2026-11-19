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
    *writes = *reads | NZ;
    return *reads != 0;
  }
  if (!strcmp(op, "add") || !strcmp(op, "sub") || !strcmp(op, "and") ||
      !strcmp(op, "addb") || !strcmp(op, "subb") || !strcmp(op, "andb") ||
      !strcmp(op, "ori") || !strcmp(op, "ore") || !strcmp(op, "orib") || !strcmp(op, "oreb")) {
    if (!regmask(a) || !regmask(b)) return false;
    *reads = regmask(a) | regmask(b);
    *writes = regmask(b) | ((!strcmp(op, "add") || !strcmp(op, "sub") ||
                            !strcmp(op, "addb") || !strcmp(op, "subb")) ? FLAGS : NZ);
    return true;
  }
  if (!strcmp(op, "inr") || !strcmp(op, "dcr") || !strcmp(op, "inrb") || !strcmp(op, "dcrb")) {
    *reads = regmask(a); *writes = *reads | NZ; return *reads != 0;
  }
  if (!strcmp(op, "ina") || !strcmp(op, "dca") || !strcmp(op, "inx") || !strcmp(op, "dcx")) {
    *reads = op[2] == 'x' ? RX : RA; *writes = *reads | NZ; return true;
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
static bool ab_barrier(lineNode *line, const char *op)
{
  return line->isLabel || line->isInline || branch_flag(op) ||
    !strcmp(op, "jmp") || !strcmp(op, "bra") || !strcmp(op, "jsr") ||
    !strcmp(op, "rsr") || !strcmp(op, "mul") || !strcmp(op, "div");
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
        if (ab_barrier(line, insn) || !effects(line, &reads, &writes)) break;
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
  if (!strcmp(kind, "independent-address"))
    return !(address_reads(src) & regmask(dst)) && !address_writes(src);
  if (!strcmp(kind, "stable-load"))
    return !address_writes(src) && (!strchr(src, '(') || !strchr(src, ')') ||
           !isdigit((unsigned char)src[1]));
  if (!strcmp(kind, "stable-memory"))
    return strchr(src, '(') && strchr(src, ')') && !address_writes(src) &&
           (address_reads(src) || strstr(src, "(_"));
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
  if ((!strcmp(op, "addb") || !strcmp(op, "subb") || !strcmp(op, "andb")) &&
      !strcmp(a, "al") && !strcmp(b, "bl")) return 1;
  if (!strcmp(op, "mul") || !strcmp(op, "div"))
    return regmask(a) && regmask(b) ? 2 : 4;
  if (!effects(line, &reads, &writes)) return 999;
  if (branch_flag(op) || !strcmp(op, "bra")) return 2;
  if (!strcmp(op, "jmp") || !strcmp(op, "jsr"))
    return strchr(a, '(') && address_reads(a) ? 2 : 3;
  if (!strncmp(op, "ld", 2) || !strncmp(op, "st", 2)) {
    const char *paren = strchr(a, '(');
    if (!paren) return !strcmp(op, "ldab") || !strcmp(op, "ldbb") ? 2 : 3;
    /* Unlike ordinary 0(r), the assembler retains an explicit 0(r+)
       displacement byte. Underestimating it can break short-branch range. */
    if (address_writes(a)) return paren == a ? 2 : 3;
    if (address_reads(a)) {
      bool zero = paren == a || (paren == a + 1 && a[0] == '0');
      if (zero) return !strcmp(op, "ldx") || !strcmp(op, "stx") ? 2 : 1;
      return 3;
    }
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
