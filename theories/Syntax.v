From FileSync Require Export
     File.

Variant F :=
  Fls    (p: path)
| Fread  (p: path)
| Fwrite (p: path) (c: content)
| Fmkdir (p: path)
| Frm    (p: path).

Variant A :=
  Als   (l: list name)
| Aread (c: content)
| Ayes
| Ano.

Variant R := R1 | R2.

Variant Q :=
  QFile (r: R) (f: F)
| QSync.

Definition S : Type := node * node * node.
