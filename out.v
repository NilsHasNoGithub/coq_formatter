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