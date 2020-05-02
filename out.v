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
                            isOkA a
                        ->
                            isOkC c
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