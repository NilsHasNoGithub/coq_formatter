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