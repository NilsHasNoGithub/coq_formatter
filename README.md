# coq_formatter
A script which formats coq definitions and theorems. Make sure the coq file does not contain syntax errors, because syntax errors lead to unspecified behavior.

## Example

` in.v `:
```
Variable A:Set.

Variable B:Set.

Variable C:Set.

Variable isOkA : A -> Prop.

Variable isOkB : B -> Prop.

Variable isOkC : C -> Prop.

Definition Def :=
forall a:A, exists b:B, isOkA a /\ isOkB b \/ (exists c:C, isOkC c -> isOkA a).

Theorem T :
forall a:A,
forall b:B,
forall c:C,
isOkA a
/\
isOkB b
\/
isOkC c
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
Variable A:Set.

Variable B:Set.

Variable C:Set.

Variable isOkA : A -> Prop.

Variable isOkB : B -> Prop.

Variable isOkC : C -> Prop.

Definition Def :=
    forall a:A,
        exists b:B,
                    isOkA a
                /\
                    isOkB b
            \/
                (
                    exists c:C,
                            isOkC c
                        ->
                            isOkA a
                )
.

Theorem T :
    forall a:A,
        forall b:B,
            forall c:C,
                            isOkA a
                        /\
                            isOkB b
                    \/
                        isOkC c
                ->
                    Def
.
```

For explanation of additional arguments run:
```
python coq_formatter.py -h
```