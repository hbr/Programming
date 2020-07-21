From Coq Require Extraction.

Module Type SORTABLE.

    Parameter T: Type.

    Inductive Comparison: Type := LT | EQV | GT.

    Parameter compare: T -> Comparison.

End SORTABLE.


Module Option.
    Definition T (A: Type): Type := option A.

    Definition map {A B: Type} (f: A -> B) (o: T A): T B :=
        match o with
        | None =>
            None
        | Some v =>
            Some (f v)
        end.
End Option.

Module RedBlack (S: SORTABLE).


    (* Basic definitions. *)

    Inductive Color: Type := Red | Black.

    Definition increase (c: Color) (h: nat): nat :=
        match c with
        | Red =>
            h
        | Black =>
            S h
        end.

    Module Tree.
        Inductive T: Type :=
        | empty: T
        | node: Color -> T -> S.T -> T -> T.

        Fixpoint blackHeight (tree: T): nat :=
            match tree with
            | empty =>
                O
            | node color t1 _ _ =>
                increase color (blackHeight t1)
            end.

        Definition color (tree: T): Color :=
            match tree with
            | empty =>
                Black
            | node c _ _ _ =>
                c
            end.
    End Tree.


    Inductive isValid: Tree.T -> Color -> nat -> Prop :=
    | validEmpty:
        isValid Tree.empty Black O

    | validRed:
        forall h t1 x t2,
            isValid t1 Black h
            -> isValid t2 Black h
            -> isValid (Tree.node Red t1 x t2) Red h

    | validBlack:
        forall h t1 c1 x t2 c2,
            isValid t1 c1 h
            -> isValid t2 c2 h
            -> isValid (Tree.node Black t1 x t2) Black (S h).


    Inductive RBT: Type :=
    | makeRBT:
        forall t c h, isValid t c h -> RBT.




    (* Insertion *)

    Definition trustMe {A: Type}: A.
    Admitted.

    Inductive Inserted: Tree.T -> Type :=
        | insOk:
            forall t0 t1,
                let h := Tree.blackHeight t0 in
                let c := Tree.color t0 in
                isValid t0 c h
                -> isValid t1 c h
                -> Inserted t0

        | insOkBlackRed:
            forall t0 t1,
                let h := Tree.blackHeight t0 in
                isValid t0 Black h
                -> isValid t1 Red h
                -> Inserted t0

        | insViolation:
            forall t0 a (x: S.T) b (y: S.T) c,
                let h := Tree.blackHeight t0 in
                isValid t0 Red h
                -> isValid a Black h
                -> isValid b Black h
                -> isValid c Black h
                -> Inserted t0.


    Definition insertedToRBT tree (ins: Inserted tree): RBT :=
        match ins with
        | insOk _ _ _ valid =>
            makeRBT _ _ _ valid

        | insOkBlackRed _ _ _ _ valid =>
            makeRBT _ _ _ valid

        | insViolation _ _ x _ y _ _ va vb vc =>
            makeRBT _ _ _
                (
                    validBlack _ _ _ x _ _
                        va
                        (validRed _ _ y _ vb vc)
                )
        end.


    Definition
        insert_aux (e: S.T) (tree: Tree.T)
        : forall c h,
            isValid tree c h
            -> option (Inserted tree)
        :=
            trustMe.



    Definition insert (e: S.T) (tree: RBT): option RBT :=
        match tree with
        | makeRBT t _ _ valid =>
            Option.map
                (insertedToRBT t)
                (insert_aux e _ _ _ valid)
        end.
End RedBlack.
