/* Centurion CPU6 port. SPDX-License-Identifier: GPL-2.0-or-later */
#include "common.h"
#include "dbuf_string.h"
#include "peep.h"

void cpu6_assignRegisters (ebbIndex *ebbi);
const char *cpu6SymbolName (symbol *sym);
extern int cpu6_stack_only;
extern int cpu6_no_tail_recursion;
extern int cpu6_no_wide_native;
extern int cpu6_bitint48;
extern int cpu6_no_autoindex;
extern int cpu6_no_byte_arithmetic;
extern int cpu6_no_divmod;
extern int cpu6_no_wide_shifts;
extern int cpu6_simple_allocation;
extern int cpu6_no_frame_base;
extern int cpu6_no_tail_calls;
extern int cpu6_keep_static_functions;
extern int cpu6_no_inline48;
extern int cpu6_no_inplace_wide;
extern int cpu6_no_ab_allocation;
extern int cpu6_no_rhs_forwarding;
void cpu6FinishFunctions (void);
void cpu6MmuEmit (FILE *);
int cpu6_no_auto_inline;
int cpu6_leaf_inline_only;
int cpu6_no_loop_strength;
int cpu6_float32;
int cpu6_mmu_metadata;
static int cpu6_no_jump_tables;

static const ASM_MAPPING cpu6_mapping[] = {
  {"labeldef", "%s:"}, {"slabeldef", "%s:"},
  {"globalfunctionlabeldef", "%s:"}, {"functionlabeldef", "%s:"},
  {"tlabeldef", "L%05d:"}, {"tlabel", "L%05d"},
  {"area", ".%s"}, {"areacode", ".%s"},
  {"areadata", ".%s"}, {"areahome", ".%s"},
  {"db", ".byte"}, {"dbs", ".byte %s"},
  {"dw", ".word"}, {"dws", ".word %s"},
  {"ds", ".ds %d"}, {"global", ".export %s"},
  {"extern", "; external %s"}, {"module", "; module %.80s"},
  {"immed", ""}, {"immedbyte", "0x%02x"}, {"immedword", "0x%04x"},
  {"hashedstr", "%s"}, {"zero", "0"}, {"one", "1"},
  {"los", "<%s"}, {"his", ">%s"},
  {NULL, NULL}
};
static const ASM_MAPPINGS cpu6_asm = {&asm_asxxxx_mapping, cpu6_mapping};
static OPTION cpu6_options[] = {
  {0, "--cpu6-no-jump-tables", &cpu6_no_jump_tables,
   "Use comparison chains for switches"},
  {0, "--cpu6-mmu-metadata", &cpu6_mmu_metadata,
   "Emit MMU cross-unit placement and address-use metadata"},
  {0, "--cpu6-float32", &cpu6_float32,
   "Enable software IEEE-754 binary32 (float only; no double)"},
  {0, "--cpu6-stack-only", &cpu6_stack_only,
   "Keep temporaries on the stack (disable CPU6 X/Y/Z allocation and peepholes)"},
  {0, "--cpu6-no-tail-recursion", &cpu6_no_tail_recursion,
   "Disable conversion of terminal self-calls into loops"},
  {0, "--cpu6-no-wide-native", &cpu6_no_wide_native,
   "Use the shared software helpers for general 32-bit operations"},
  {0, "--cpu6-bitint48", &cpu6_bitint48,
   "Enable native signed/unsigned _BitInt(48) scalars"},
  {0, "--cpu6-no-autoindex", &cpu6_no_autoindex,
   "Disable the CPU6 auto-index peepholes for comparison"},
  {0, "--cpu6-no-byte-arithmetic", &cpu6_no_byte_arithmetic,
   "Use word operations for byte results (for comparison)"},
  {0, "--cpu6-no-auto-inline", &cpu6_no_auto_inline,
   "Disable automatic inlining of small functions (keep explicit inline)"},
  {0, "--cpu6-leaf-inline-only", &cpu6_leaf_inline_only,
   "Restrict automatic inlining to leaf functions"},
  {0, "--cpu6-no-divmod", &cpu6_no_divmod,
   "Disable common quotient/remainder computation"},
  {0, "--cpu6-no-wide-shifts", &cpu6_no_wide_shifts,
   "Use runtime helpers for constant 32-bit shifts"},
  {0, "--cpu6-simple-allocation", &cpu6_simple_allocation,
   "Use conservative intervals and function-wide X saves"},
  {0, "--cpu6-no-frame-base", &cpu6_no_frame_base,
   "Do not reserve Z for a hot window in a large stack frame"},
  {0, "--cpu6-no-tail-calls", &cpu6_no_tail_calls,
   "Disable terminal jumps to other functions"},
  {0, "--cpu6-keep-static-functions", &cpu6_keep_static_functions,
   "Retain unused out-of-line static function bodies"},
  {0, "--cpu6-no-inline48", &cpu6_no_inline48,
   "Use library calls for scalar 48-bit addition/subtraction"},
  {0, "--cpu6-no-inplace-wide", &cpu6_no_inplace_wide,
   "Disable direct updates of nonvolatile 32/48-bit objects"},
  {0, "--cpu6-no-loop-strength", &cpu6_no_loop_strength,
   "Disable target-costed word induction strength reduction"},
  {0, "--cpu6-no-ab-allocation", &cpu6_no_ab_allocation,
   "Disable late A/B live-range allocation and coalescing"},
  {0, "--cpu6-no-rhs-forwarding", &cpu6_no_rhs_forwarding,
   "Disable forwarding single-use word right operands in B"},
  {0, NULL}
};
static char *cpu6_keywords[] = {NULL};
static const char *cpu6_as[] = {"asee200", "-o", "$1.o", "$1.s", NULL};
static char cpu6_rules[] = {
#include "peep.rul"
  ""
};

static void cpu6_init (void) { asm_addTree (&cpu6_asm); }
static bool cpu6_parse (int *argc, char **argv, int *index)
{
  (void)argc; (void)argv; (void)index;
  return false;
}
static void cpu6_defaults (void)
{
  options.stackAuto = 1;
  options.noRegParams = 1;
  options.intlong_rent = options.float_rent = 1;
  options.signed_char = 0;
  options.nopeep = 0;
}
static void cpu6_finalize (void)
{
  if (cpu6_no_jump_tables) port->jumptableCost.maxCount = 0;
  if (cpu6_float32) addSet (&preArgvSet, Safe_strdup ("-D__CPU6_FLOAT32__=1"));
  if (cpu6_bitint48) port->s.bitint_maxwidth = 48;
  port->mem.default_local_map = data;
  port->mem.default_globl_map = data;
}
static void cpu6_start (FILE *out)
{
  /* Fuzix .export declares definitions; undefined references are implicit. */
  set *imports = NULL;
  symbol *sym;
  for (sym = setFirstItem (publics); sym; sym = setNextItem (publics))
    if (IS_FUNC (sym->type) && !IFFUNC_HASBODY (sym->type)) addSet (&imports, sym);
  for (sym = setFirstItem (imports); sym; sym = setNextItem (imports))
    deleteSetItem (&publics, sym);
  deleteSet (&imports);
  fprintf (out, "\t.setcpu 6\n");
  cpu6MmuEmit (out);
}
static unsigned cpu6_arg_position;
static bool cpu6_register_arguments;
static void cpu6_reset_params (sym_link *type)
{
  cpu6_arg_position = 0;
  if (FUNC_SDCCCALL (type) > 1) {
    fprintf (stderr, "cpu6: only __sdcccall(0) and __sdcccall(1) are supported\n");
    exit (1);
  }
  cpu6_register_arguments = FUNC_SDCCCALL (type) == 1 && !IFFUNC_HASVARARGS (type);
}
static int cpu6_param (sym_link *type, bool reentrant)
{
  (void)reentrant;
  if (!cpu6_register_arguments || cpu6_arg_position >= 2) return 0;
  if (getSize (type) > 2 || (!IS_INTEGRAL (type) && !IS_PTR (type))) {
    cpu6_register_arguments = false; return 0;
  }
  return ++cpu6_arg_position; /* first word in A, second word in B */
}
static bool cpu6_native (iCode *ic, sym_link *left, sym_link *right)
{
  (void)ic;
  return IS_INTEGRAL (left) && IS_INTEGRAL (right) &&
    getSize (left) <= (cpu6_bitint48 ? 6 : 4) && getSize (right) <= (cpu6_bitint48 ? 6 : 4);
}
static bool cpu6_ext_bitop (int op, sym_link *type, int right)
{
  (void)op; (void)type; (void)right;
  return false;
}
static const char *cpu6_reg_name (const struct reg_info *reg)
{
  (void)reg;
  return "";
}
static void cpu6_finish_areas (FILE *out, bool has_main)
{
  (void)out; (void)has_main;
  cpu6FinishFunctions ();
}
static void cpu6_glue (void)
{
  /* The installed EE200 object format retains 16 significant name bytes.
     Mangle private definitions as well as their code references. Public
     spellings retain the existing FCC/assembler ABI. */
  memmap *maps[] = {data, statsg, code};
  for (unsigned i = 0; i < sizeof (maps) / sizeof (maps[0]); i++)
    for (symbol *entry = setFirstItem (maps[i]->syms); entry; entry = setNextItem (maps[i]->syms))
      if (IS_STATIC (entry->etype) || entry->isstrlit) cpu6SymbolName (entry);
  /* RAM is loaded from the executable. Emit initial values directly; keep
     zero-initialized objects in BSS for the shared CRT to clear. */
  set *move = NULL;
  symbol *sym;
  for (sym = setFirstItem (data->syms); sym; sym = setNextItem (data->syms))
    if (sym->ival && !IS_FUNC (sym->type)) addSet (&move, sym);
  for (sym = setFirstItem (move); sym; sym = setNextItem (move))
    {
      deleteSetItem (&data->syms, sym);
      addSet (&statsg->syms, sym);
    }
  deleteSet (&move);
  glue ();
}

PORT cpu6_port = {
  .id = TARGET_ID_CPU6,
  .target = "cpu6",
  .target_name = "Centurion CPU6",
  .general = {cpu6_glue, false, MODEL_SMALL, MODEL_SMALL, NULL},
  .assembler = {.cmd = cpu6_as, .file_ext = ".s"},
  .linker = {.rel_ext = ".o"},
  .peep = {.default_rules = cpu6_rules, .getSize = cpu6instructionSize,
           .notUsed = cpu6notUsed, .notUsedFrom = cpu6notUsedFrom,
           .canAssign = cpu6canAssign},
  /* Only ordinary 8/16/32-bit integers are lowered. Advertising _BitInt
     would let generalized constant propagation invent unsupported 24-bit
     temporaries, e.g. for a 16-bit limb plus a carry. */
  .s = {1, 2, 2, 4, 8, 2, 2, 2, 2, 2, 1, 4, 0},
  .mem = {
    .xstack_name = "bss", .istack_name = "bss",
    .code_name = "code", .data_name = "bss", .reg_name = "bss",
    .static_name = "data", .post_static_name = "code",
    .home_name = "code", .const_name = "data",
    .cabs_name = "code", .xabs_name = "data", .iabs_name = "data",
    .code_ro = 0, .maxextalign = 1
  },
  .stack = {.direction = -1, .call_overhead = 2, .offset = 0},
  .extraAreas = {.genExtraAreaDeclaration = cpu6_finish_areas},
  .support = {.shift = -1},
  .jumptableCost = {.maxCount = 256, .sizeofElement = 2,
                    .sizeofMatchJump = {8, 8, 12}, .sizeofRangeCompare = {8, 8, 14},
                    .sizeofSubtract = 4, .sizeofDispatch = 9},
  .fun_prefix = "_",
  .init = cpu6_init,
  .parseOption = cpu6_parse,
  .poptions = cpu6_options,
  .finaliseOptions = cpu6_finalize,
  .setDefaultOptions = cpu6_defaults,
  .assignRegisters = cpu6_assignRegisters,
  .getRegName = cpu6_reg_name,
  .keywords = cpu6_keywords,
  .genAssemblerStart = cpu6_start,
  .reset_regparms = cpu6_reset_params,
  .reg_parm = cpu6_param,
  .hasNativeMulFor = cpu6_native,
  .hasExtBitOp = cpu6_ext_bitop,
  .use_dw_for_init = true,
  .little_endian = false,
  .c_preamble = "extern unsigned __cpu6_asm16(const char *, unsigned) __builtin__;\n"
                "extern unsigned __cpu6_asm16_2(const char *, unsigned, unsigned) __builtin__;\n",
  .unqualified_pointer = GPOINTER,
  .reset_labelKey = 0,
  .globals_allowed = 1,
  .num_regs = 0,
  .magic = PORT_MAGIC
};
