# coq_formatter
A script which formats coq definitions and theorems. Make sure the coq file does not contain syntax errors, because syntax errors lead to unspecified behavior.

## Example

` in.v `:
```
Definition Def :=
forall a:A, exists b:B, a /\ b \/ (exists c:C, c -> A).

Theorem T:
forall a:A,
forall b:B,
forall c:C,
a
/\
b
\/
c
->
Def
.
```

To format `in.v` run:

```
python coq_formatter.py in.v out.v
```

Which results in the following `out.v`:
```
Definition Def :=
    forall a:A,
        exists b:B,
                    a
                /\
                    b
            \/
                (
                    exists c:C,
                            c
                        ->
                            A
                )
.

Theorem T:
    forall a:A,
        forall b:B,
            forall c:C,
                            a
                        /\
                            b
                    \/
                        c
                ->
                    Def
.
```

For explanation of additional arguments run:
```
python coq_formatter.py -h
```