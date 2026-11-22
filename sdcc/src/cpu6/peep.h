/* SPDX-License-Identifier: GPL-2.0-or-later */
bool cpu6notUsed(const char *what, lineNode *end, lineNode *head);
bool cpu6notUsedFrom(const char *what, const char *label, lineNode *head);
bool cpu6canAssign(const char *dst, const char *src, const char *kind);
int cpu6instructionSize(lineNode *line);
bool cpu6AllocateAB(lineNode *head);
bool cpu6OptimizeLoops(lineNode *head);
void cpu6FinalizeBranches(lineNode *head);
bool cpu6OperandAsm(const char *text);
