/* CPU6 MMU placement metadata and source-level address lifetime diagnostics.
   SPDX-License-Identifier: GPL-2.0-or-later */
#include "common.h"
#include "SDCCattr.h"

extern const char *cpu6SymbolName (symbol *);
static set *declarations;

typedef struct mmu_escape {
  symbol *sym;
  const char *file;
  int line;
  struct mmu_escape *next;
} mmu_escape;
static mmu_escape *escapes;

void cpu6MmuAttribute (symbol *sym, attribute *attributes)
{
  for (attribute *a = attributes; a; a = a->next)
    if (!strcmp (a->token_string, "mmu_page")) {
      int page = atoi (a->argument_clause);
      if (!TARGET_IS_CPU6 || !page)
        werror (E_SYNTAX_ERROR, "mmu_page is a CPU6 placement attribute");
      if (sym->cpu6_mmu_page && sym->cpu6_mmu_page != page)
        werror (E_SYNTAX_ERROR, "conflicting mmu_page attributes");
      sym->cpu6_mmu_page = page;
      addSet (&declarations, sym);
    }
}

static symbol *root_object (ast *tree)
{
  if (IS_AST_SYM_VALUE (tree)) return AST_SYMBOL (tree);
  if (IS_ARRAY_OP (tree) || IS_ADDRESS_OF_OP (tree)) return root_object (tree->left);
  if (IS_AST_OP (tree) && tree->opval.op == PTR_OP && IS_ADDRESS_OF_OP (tree->left))
    return root_object (tree->left->left);
  return NULL;
}

static void record_escape (ast *tree, symbol *sym)
{
  if (!sym || (sym->level && !IS_STATIC (sym->etype)) || sym->isstrlit || sym->isitmp || sym->_isparm) return;
  for (mmu_escape *e = escapes; e; e = e->next)
    if (e->sym == sym && e->line == tree->lineno && e->file == tree->filename) return;
  if (sym->cpu6_mmu_page)
    werrorfl (tree->filename, tree->lineno, E_SYNTAX_ERROR,
              "address/array decay/function pointer of an MMU object is forbidden");
  mmu_escape *entry = Safe_alloc (sizeof (*entry));
  entry->sym = sym;
  entry->file = tree->filename;
  entry->line = tree->lineno;
  entry->next = escapes;
  escapes = entry;
}

static void scan (ast *tree, ast *parent)
{
  if (!tree) return;
  if (IS_AST_OP (tree) && (tree->opval.op == SIZEOF || tree->opval.op == COUNTOF)) return;
  if (tree->cpu6_user_address) record_escape (tree, root_object (tree->left));
  if (!IS_AST_VALUE (tree) && tree->ftype && IS_ARRAY (tree->ftype) &&
      !(IS_ARRAY_OP (parent) && parent->left == tree))
    record_escape (tree, root_object (tree));
  if (IS_AST_SYM_VALUE (tree) && !(IS_AST_OP (parent) &&
      (parent->opval.op == PTR_OP || parent->opval.op == '.') && parent->right == tree)) {
    symbol *sym = AST_SYMBOL (tree);
    if (IS_ARRAY (sym->type) && !(IS_ARRAY_OP (parent) && parent->left == tree))
      record_escape (tree, sym);
    if (IS_FUNC (sym->type) && !(IS_CALLOP (parent) && parent->left == tree))
      record_escape (tree, sym);
  }
  if (IS_FOR_STMT (tree)) {
    scan (AST_FOR (tree, initExpr), tree);
    scan (AST_FOR (tree, condExpr), tree);
    scan (AST_FOR (tree, loopExpr), tree);
  }
  scan (tree->left, tree);
  scan (tree->right, tree);
}

void cpu6MmuScan (ast *tree) { scan (tree, NULL); }

static void scan_initializer (initList *init)
{
  for (; init; init = init->next)
    if (init->type == INIT_DEEP) scan_initializer (init->init.deep);
    else if (init->type == INIT_NODE) scan (init->init.node, NULL);
}

void cpu6MmuEmit (FILE *out)
{
  extern int cpu6_float32, cpu6_mmu_metadata;
  /* Ordinary compilations keep their original assembly, including comments.
     The MMU driver requests metadata for unannotated cross-unit callers too. */
  if (!cpu6_mmu_metadata && !declarations) return;
  fprintf (out, "; CPU6 MMU V 1 float32=%d\n", cpu6_float32 != 0);
  memmap *maps[] = {data, statsg, code};
  for (unsigned i = 0; i != sizeof (maps) / sizeof (maps[0]); ++i)
    for (symbol *sym = setFirstItem (maps[i]->syms); sym; sym = setNextItem (maps[i]->syms))
      if (sym->ival) scan_initializer (sym->ival);
  for (symbol *original = setFirstItem (declarations); original; original = setNextItem (declarations)) {
    symbol *sym = findSymWithLevel (SymbolTab, original);
    if (!sym) sym = original;
    if ((sym->level && !IS_STATIC (sym->etype)) || sym->_isparm || IS_TYPEDEF (sym->etype)) {
      werrorfl (sym->fileDef, sym->lineDef, E_SYNTAX_ERROR,
                "mmu_page requires a function or an object with static storage duration");
      continue;
    }
    fprintf (out, "; CPU6 MMU D %s %d %s %u %s:%d\n", cpu6SymbolName (sym),
             original->cpu6_mmu_page, IS_FUNC (sym->type) ? "function" :
             IS_CONSTANT (sym->etype) && !IS_PTR (sym->type) ? "constant" : "object",
             IS_FUNC (sym->type) ? 0 : getSize (sym->type),
             sym->fileDef ? sym->fileDef : "?", sym->lineDef);
  }
  for (mmu_escape *e = escapes; e; e = e->next) {
    symbol *sym = findSymWithLevel (SymbolTab, e->sym);
    if (!sym) sym = e->sym;
    if (sym->cpu6_mmu_page)
      werrorfl (e->file, e->line, E_SYNTAX_ERROR,
                "address/array decay/function pointer of an MMU object is forbidden");
    fprintf (out, "; CPU6 MMU E %s %s:%d\n", cpu6SymbolName (sym),
             e->file ? e->file : "?", e->line);
  }
}
