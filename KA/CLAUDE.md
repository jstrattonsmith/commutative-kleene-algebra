# KA/ style guidelines

- Use **ssreflect** tactics (`move=>`, `rewrite`, `apply/`, `case/`, `elim:`,
  `/=`) extensively. Avoid `destruct`, `induction`, `exfalso`, etc. This
  applies to `KA/` (files 9-18 in the root `CLAUDE.md`'s File Structure
  section). The `MM2_Legacy/` and `CKAUndec/` files deliberately use plain Coq
  tactics instead (`intros`, `destruct`, `apply`) -- they interface
  directly with `coq-synthetic-computability`'s own plain-tactic style,
  and mixing ssreflect in at that boundary wasn't worth the friction.
