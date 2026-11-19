# SDCC for Centurion CPU6

This branch ports SDCC 4.6.4 to the Centurion CPU6. It starts at SDCC SVN
r17105, Git commit `f966b0004c76eb960ce61c06fabecacf3916aa94`. The
`master` branch records the original revision. [SDCC mirror](https://repo.or.cz/sdcc.git)

- The CPU6 backend emits EE200 assembler for a big-endian, 16-bit target.
  It uses CPU6 word multiply and divide, multiword arithmetic, X/Y/Z
  allocation, an optional A/B calling convention and liveness-aware peepholes.
- The optimizer adds auto-indexing, jump tables, tail calls, loop strength
  reduction and forwarding into A/B. The distribution drivers add
  assembly-level cross-file inlining and link-time section GC.
- Opt-in modes add software IEEE-754 binary32 and native 48-bit integers.
  The frontend accepts CPU6 MMU placement attributes and operand-aware inline
  assembly. The distribution supplies the corresponding runtimes and drivers.
- The Centurion checkout retains the compiler, preprocessor, and libiberty
  build inputs. The other targets' device libraries, simulators and unused
  binutils sources are available in the original tree.

The existing SDCC and preprocessor licenses and per-file notices apply.
See [SDCC COPYING](sdcc/COPYING) and [SDCC licensing documentation](sdcc/doc/README.txt).
