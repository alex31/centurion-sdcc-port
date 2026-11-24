/* GCC-compatible CPU6 bit builtins. SPDX-License-Identifier: GPL-2.0-or-later */
#include <stdint.h>
#include "common.h"
#include "bitbuiltins.h"

/* Each public operation reduces to one primitive. Complementing the input
   takes place at its original precision; some results need one final
   arithmetic operation. The argument subtrees each occur exactly once. */
typedef enum { POP, CLZ, CTZ, CLRSB, CEIL, FLOOR, ROTL, ROTR, SWAP } primitive;
typedef enum { COUNT, PARITY, FIRST, WIDTH_MINUS, SINGLE, SAME } result_op;

typedef struct {
  const char *name;
  primitive core;
  result_op result;
  unsigned bits;       /* Zero for the type-generic spellings. */
  bool signed_arg;
  bool invert;
} bit_builtin;

#define FIXED(name, op, result, signed_arg) \
  {#name, op, result, 16, signed_arg}, {#name "l", op, result, 32, signed_arg}, \
  {#name "ll", op, result, 64, signed_arg}, {#name "g", op, result, 0, signed_arg}

static const bit_builtin operations[] = {
  FIXED (ffs, CTZ, FIRST, true),
  FIXED (clz, CLZ, COUNT, false),
  FIXED (ctz, CTZ, COUNT, false),
  FIXED (clrsb, CLRSB, COUNT, true),
  FIXED (popcount, POP, COUNT, false),
  FIXED (parity, POP, PARITY, false),
  {"bswap16", SWAP, SAME, 16}, {"bswap32", SWAP, SAME, 32},
  {"stdc_bit_ceil", CEIL, SAME}, {"stdc_bit_floor", FLOOR, SAME},
  {"stdc_bit_width", CLZ, WIDTH_MINUS}, {"stdc_has_single_bit", POP, SINGLE},
  {"stdc_rotate_left", ROTL, SAME}, {"stdc_rotate_right", ROTR, SAME},
  {"stdc_count_ones", POP, COUNT}, {"stdc_count_zeros", POP, WIDTH_MINUS},
  {"stdc_leading_zeros", CLZ, COUNT}, {"stdc_trailing_zeros", CTZ, COUNT},
  {"stdc_first_leading_one", CLZ, FIRST}, {"stdc_first_trailing_one", CTZ, FIRST},
  {"stdc_leading_ones", CLZ, COUNT, 0, false, true},
  {"stdc_trailing_ones", CTZ, COUNT, 0, false, true},
  {"stdc_first_leading_zero", CLZ, FIRST, 0, false, true},
  {"stdc_first_trailing_zero", CTZ, FIRST, 0, false, true},
};

static const bit_builtin *
operation (const ast *tree)
{
  if (!IS_CALLOP (tree) || !IS_AST_SYM_VALUE (tree->left))
    return NULL;
  const char *name = AST_SYMBOL (tree->left)->name;
  if (strncmp (name, "__builtin_", 10))
    return NULL;
  for (unsigned i = 0; i < sizeof (operations) / sizeof (*operations); i++)
    if (!strcmp (name + 10, operations[i].name))
      return &operations[i];
  return NULL;
}

bool
cpu6IsBitBuiltin (const ast *tree)
{
  return operation (tree) != NULL;
}

static ast *
literal (sym_link *type, uint64_t value)
{
  return newAst_VALUE (valCastLiteral (type, (double)value, value));
}

static ast *
convert (sym_link *type, ast *expr)
{
  return newNode (CAST, newAst_LINK (copyLinkChain (type)), expr);
}

static uint64_t
bitmask (unsigned bits)
{
  return UINT64_MAX >> (64 - bits);
}

static uint64_t
fold (const bit_builtin *op, unsigned bits, uint64_t x, uint64_t extra)
{
  uint64_t mask = bitmask (bits);
  x &= mask;
  if (op->invert)
    x ^= mask;
  uint64_t result = 0;
  unsigned count = extra % bits;
  uint64_t high = UINT64_C(1) << (bits - 1);
  switch (op->core)
    {
    case POP:
      while (x) { x &= x - 1; result++; }
      break;
    case CLRSB:
      if (x & high) x ^= mask;
      high >>= 1;
      while (high && !(x & high)) { high >>= 1; result++; }
      break;
    case CLZ:
      if (!x) result = extra;
      else while (!(x & high)) { high >>= 1; result++; }
      break;
    case CTZ:
      if (!x) result = extra;
      else while (!(x & 1)) { x >>= 1; result++; }
      break;
    case FLOOR:
      if (x) { while (!(x & high)) high >>= 1; result = high; }
      break;
    case CEIL:
      if (x <= 1) result = 1;
      else { x--; while (!(x & high)) high >>= 1; result = (high << 1) & mask; }
      break;
    case ROTL:
      result = count ? ((x << count) | (x >> (bits - count))) & mask : x;
      break;
    case ROTR:
      result = count ? ((x >> count) | (x << (bits - count))) & mask : x;
      break;
    case SWAP:
      for (unsigned i = 0; i < bits; i += 8) { result = (result << 8) | (x & 255); x >>= 8; }
      break;
    }
  switch (op->result)
    {
    case FIRST: return result + 1;
    case WIDTH_MINUS: return bits - result;
    case PARITY: return result & 1;
    case SINGLE: return result == 1;
    default: return result;
    }
}

static sym_link *
unsignedType (unsigned bits)
{
  if (bits <= 8) return UCHARTYPE;
  if (bits <= 16) return UINTTYPE;
  if (bits <= 32) return ULONGTYPE;
  if (bits == 48)
    {
      sym_link *type = newBitIntLink (48);
      SPEC_USIGN (type) = 1;
      return type;
    }
  return ULONGLONGTYPE;
}

/* Helper parameters have a canonical unsigned type so unsigned short,
   unsigned int and unsigned _BitInt(16) can share a single ABI. */
static ast *
helper (const char *name, bool builtin, sym_link *ret, ast *first, sym_link *a1,
        ast *second, sym_link *a2, unsigned field_width)
{
  symbol *sym = findSym (SymbolTab, NULL, name);
  if (!sym)
    {
      sym = second ? funcOfType2 (name, ret, a1, a2, options.stackAuto) :
                     funcOfType (name, ret, a1, 1, options.stackAuto);
      if (field_width)
        {
          value *last = newValue ();
          last->type = last->etype = copyLinkChain (UINTTYPE);
          FUNC_ARGS (sym->type)->next->next = last;
        }
      FUNC_ISBUILTIN (sym->type) = builtin;
    }
  if (field_width)
    second = newNode (PARAM, second, literal (UINTTYPE, field_width));
  ast *call = newNode (CALL, newAst_VALUE (symbolVal (sym)),
                       second ? newNode (PARAM, first, second) : first);
  call->left->funcName = 1;
  return call;
}

static ast *
rotateCount (ast *count, unsigned bits)
{
  if (IS_AST_LIT_VALUE (count))
    return literal (UINTTYPE, ullFromVal (AST_VALUE (count)) % bits);
  if (!(bits & (bits - 1)))
    return newNode ('&', convert (UINTTYPE, count), literal (UINTTYPE, bits - 1));
  /* For 48-bit words and bit-fields, narrowing the count before modulo
     would lose significant bits. */
  if (bitsForType (count->ftype) == 64)
    return helper ("__c6_modcnt64", false, UINTTYPE, count, ULONGLONGTYPE,
                   literal (UINTTYPE, bits), UINTTYPE, 0);
  return convert (UINTTYPE, newNode ('%', count, literal (UINTTYPE, bits)));
}

static ast *
expand (const bit_builtin *op, unsigned bits, ast *x, ast *extra)
{
  static const char *const names[] = {"pop", "clz", "ctz", "clrsb", "ceil", "floor", "rotl", "rotr", "bswap"};
  sym_link *word = unsignedType (bits);
  unsigned storage = bitsForType (word);
  bool rotation = op->core == ROTL || op->core == ROTR;
  bool field = storage != bits;
  char name[32];
  bool builtin = op->core == SWAP || (rotation && !field && bits <= 32);
  bool callee_returns_word = op->result == SAME;
  x = convert (word, x);
  if (op->invert)
    x = convert (word, newNode ('~', x, NULL));
  if (field && op->core != CLRSB)
    {
      x = newNode ('&', x, literal (word, bitmask (bits)));
      if (op->core == CLZ)
        x = convert (word, newNode (LEFT_OP, x, literal (UINTTYPE, storage - bits)));
    }
  if (op->result == SINGLE && storage <= 16)
    {
      snprintf (name, sizeof (name), "__cpu6_single%u", storage);
      return helper (name, true, newBoolLink (), x, word, NULL, NULL, 0);
    }
  if (rotation)
    extra = rotateCount (extra, bits);
  if (rotation && field)
    snprintf (name, sizeof (name), "__c6_%sfield", names[op->core]);
  else
    snprintf (name, sizeof (name), "%s%s%u", (rotation || builtin) ? "__cpu6_" : "__c6_",
              names[op->core], storage);
  sym_link *argtype = rotation && field ? UINTTYPE : word;
  ast *val = helper (name, builtin, callee_returns_word ? argtype : INTTYPE,
                     x, argtype, extra, rotation ? UINTTYPE : INTTYPE, rotation && field ? bits : 0);
  /* The input conversion sign-extends a signed bit-field. The primitive
     counts the redundant padding bits along with the field's own bits. */
  if (field && op->core == CLRSB)
    val = newNode ('-', val, literal (INTTYPE, storage - bits));
  if (field && op->core == CEIL)
    val = newNode ('&', val, literal (UINTTYPE, bitmask (bits)));
  switch (op->result)
    {
    case FIRST: return newNode ('+', val, literal (INTTYPE, 1));
    case WIDTH_MINUS: return newNode ('-', literal (UINTTYPE, bits), val);
    case PARITY: return newNode ('&', val, literal (INTTYPE, 1));
    case SINGLE: return newNode (EQ_OP, val, literal (INTTYPE, 1));
    default: return val;
    }
}

static ast *
argument (ast *expr)
{
  expr = decorateType (expr, RESULT_TYPE_NONE, false);
  if (!expr->isError && IS_AST_SYM_VALUE (expr) && IS_CONSTEXPR (expr->ftype) && !IS_VOLATILE (expr->ftype))
    expr = decorateType (newAst_VALUE (constExprValue (expr, true)), RESULT_TYPE_NONE, false);
  return expr;
}

static ast *
invalid (ast *call, const char *why)
{
  char message[SDCC_NAME_MAX + 128];
  snprintf (message, sizeof (message), "%s (%s)", AST_SYMBOL (call->left)->name, why);
  werrorfl (call->filename, call->lineno, E_NOT_ALLOWED, message);
  call->ftype = call->etype = newIntLink ();
  call->isError = call->decorated = 1;
  return call;
}

ast *
cpu6DecorateBitBuiltin (ast *call)
{
  const bit_builtin *op = operation (call);
  bool rotation = op->core == ROTL || op->core == ROTR;
  bool generic = !op->bits;
  bool stdc = !strncmp (op->name, "stdc_", 5);
  bool optional = !strcmp (op->name, "clzg") || !strcmp (op->name, "ctzg");
  ast *x = call->right;
  ast *extra = NULL;
  if (IS_AST_PARAM (x)) { extra = x->right; x = x->left; }
  if (!x || IS_AST_PARAM (extra) || (rotation && !extra) || (extra && !rotation && !optional))
    return invalid (call, "invalid argument count");
  x = argument (x);
  if (x->isError) return x;
  sym_link *type = x->ftype;
  if (generic)
    {
      if (!IS_INTEGRAL (type) || IS_BOOLEAN (type) || SPEC_ENUM (type) ||
          (IS_CHAR (type) && SPEC_IMPLICIT_SIGN (type)) || IS_UNSIGNED (type) == op->signed_arg)
        return invalid (call, op->signed_arg ? "expected a signed integer" : "expected an unsigned integer");
    }
  else if (!IS_ARITHMETIC (type))
    return invalid (call, "expected an arithmetic operand");

  unsigned bits = generic ? bitsForType (type) : op->bits;
  if (bits != 8 && bits != 16 && bits != 32 && bits != 48 && bits != 64 &&
      !(IS_BITFIELD (type) && bits >= 1 && bits <= 16))
    return invalid (call, "unsupported CPU6 integer precision");
  sym_link *word = unsignedType (bits);
  if (!generic)
    {
      sym_link *declared = copyLinkChain (word);
      SPEC_USIGN (declared) = !op->signed_arg;
      x = decorateType (convert (declared, x), RESULT_TYPE_NONE, false);
    }
  if (extra)
    {
      extra = argument (extra);
      if (extra->isError) return extra;
      sym_link *t = extra->ftype;
      if (!IS_INTEGRAL (t) || (rotation && SPEC_ENUM (t)))
        return invalid (call, "expected integer second argument");
      if (optional && (IS_BITINT (t) || (bitsForType (t) > bitsForType (INTTYPE)) ||
          (bitsForType (t) == bitsForType (INTTYPE) && IS_UNSIGNED (t))))
        return invalid (call, "expected int fallback");
    }
  else if (op->core == CLZ || op->core == CTZ)
    extra = literal (INTTYPE, op->result == FIRST ? -1 : bits);

  sym_link *result = stdc ? UINTTYPE : INTTYPE;
  if (op->result == SAME)
    result = generic ? type : word;
  else if (op->result == SINGLE)
    result = newBoolLink ();
  /* The result is an rvalue. In particular a constant first argument and
     a variable count must not turn the rotate result into an S_LITERAL. */
  result = copyLinkChain (result);
  removeQualifiers (result);
  SPEC_SCLS (result) = S_FIXED;
  SPEC_CONSTEXPR (result) = 0;

  if (IS_AST_LIT_VALUE (x) && (!extra || IS_AST_LIT_VALUE (extra)))
    {
      uint64_t value = fold (op, bits, ullFromVal (AST_VALUE (x)),
                             extra ? ullFromVal (AST_VALUE (extra)) : 0);
      return decorateType (literal (result, value), RESULT_TYPE_NONE, false);
    }

  ast *tree = expand (op, bits, x, extra);
  tree = convert (result, tree);
  tree->filename = call->filename;
  tree->lineno = call->lineno;
  return decorateType (tree, RESULT_TYPE_NONE, false);
}
