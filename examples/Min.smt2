; This file works fine with 4.8.5,
; but z3 master (+ patch) fails with incomplete quantifiers

(set-option :global-decls false)
(set-option :smt.mbqi false)
(set-option :auto_config false)
(set-option :produce-unsat-cores true)
; 4.8.5 also won't work without this?
(set-option :smt.case_split 3)
(set-option :smt.arith.solver 2)
; can be omitted

(declare-sort Term)
(declare-fun Term_constr_id (Term) Int)
(declare-datatypes () ((Fuel (ZFuel) (SFuel (prec Fuel)))))
(declare-fun MaxIFuel () Fuel)
(declare-fun Valid (Term) Bool)
(declare-fun HasTypeFuel (Fuel Term Term) Bool)
(define-fun HasTypeZ ((x Term) (t Term)) Bool (HasTypeFuel ZFuel x t))
(define-fun HasType ((x Term) (t Term)) Bool (HasTypeFuel MaxIFuel x t))
(assert
  (forall
    ((f Fuel) (x Term) (t Term))
    (!
      (= (HasTypeFuel (SFuel f) x t) (HasTypeZ x t))
      :pattern
      ((HasTypeFuel (SFuel f) x t)))))
(declare-fun ApplyTT (Term Term) Term)
(declare-fun Tm_type () Term)
(declare-fun Tm_unit () Term)
(declare-fun BoxInt (Int) Term)
(declare-fun BoxBool_proj_0 (Term) Bool)
(declare-fun Prims.hasEq (Term) Term)
(declare-fun Prims.eqtype () Term)
(declare-fun Tm_refine_414d0a9f578ab0048252f8c8f552b99f () Term)
(assert
  (forall
    ((@u0 Fuel) (@x1 Term))
    (!
      (iff
        (HasTypeFuel @u0 @x1 Tm_refine_414d0a9f578ab0048252f8c8f552b99f)
        (and (HasTypeFuel @u0 @x1 Tm_type) (Valid (Prims.hasEq @x1))))
      :pattern
      ((HasTypeFuel @u0 @x1 Tm_refine_414d0a9f578ab0048252f8c8f552b99f)))))
(assert (= Prims.eqtype Tm_refine_414d0a9f578ab0048252f8c8f552b99f))
(declare-fun Prims.bool () Term)

(declare-fun Prims.pure_post (Term) Term)
(declare-fun Prims.int () Term)

(assert (HasType Prims.int Prims.eqtype))
(declare-fun Prims.exn () Term)

(declare-fun FStar.Pervasives.Native.option (Term) Term)

(declare-fun FStar.Pervasives.Native.None (Term) Term)
(declare-fun FStar.Pervasives.Native.None_a (Term) Term)
(declare-fun FStar.Pervasives.Native.None@tok () Term)

(declare-fun FStar.Pervasives.Native.Some (Term Term) Term)
(declare-fun FStar.Pervasives.Native.Some_a (Term) Term)
(declare-fun FStar.Pervasives.Native.Some_v (Term) Term)
(declare-fun FStar.Pervasives.Native.Some@tok () Term)

(define-fun
  is-FStar.Pervasives.Native.option
  ((__@x0 Term))
  Bool
  (and
    (= (Term_constr_id __@x0) 101)
    (exists
      ((@x0 Term))
      (= __@x0 (FStar.Pervasives.Native.option @x0)))))

(define-fun
  is-FStar.Pervasives.Native.None
  ((__@x0 Term))
  Bool
  (and
    (= (Term_constr_id __@x0) 108)
    (= __@x0 (FStar.Pervasives.Native.None (FStar.Pervasives.Native.None_a __@x0)))))

(define-fun
  is-FStar.Pervasives.Native.Some
  ((__@x0 Term))
  Bool
  (and
    (= (Term_constr_id __@x0) 113)
    (=
      __@x0
      (FStar.Pervasives.Native.Some
        (FStar.Pervasives.Native.Some_a __@x0)
        (FStar.Pervasives.Native.Some_v __@x0)))))

(declare-fun FStar.Pervasives.Native.uu___is_None (Term Term) Term)
(declare-fun FStar.Pervasives.Native.uu___is_Some (Term Term) Term)

(assert
  (forall
    ((@x0 Term))
    (!
      (implies
        (HasType @x0 Tm_type)
        (forall
          ((@x1 Term))
          (implies
            (HasType @x1 (FStar.Pervasives.Native.option @x0))
            (or
              (BoxBool_proj_0
                (FStar.Pervasives.Native.uu___is_None @x0 @x1))
              (BoxBool_proj_0 (FStar.Pervasives.Native.uu___is_Some @x0 @x1))))))
      :pattern
      ((FStar.Pervasives.Native.option @x0))
)))

(declare-fun FStar.Tactics.Types.proofstate () Term)
(declare-fun FStar.Tactics.Result.__result (Term) Term)
(declare-fun FStar.Tactics.Result.__result@x0 (Term) Term)
(declare-fun FStar.Tactics.Result.__result@tok () Term)
(declare-fun FStar.Tactics.Result.Success (Term Term Term) Term)
(declare-fun FStar.Tactics.Result.Success_a (Term) Term)
(declare-fun FStar.Tactics.Result.Success_v (Term) Term)
(declare-fun FStar.Tactics.Result.Success_ps (Term) Term)
(declare-fun FStar.Tactics.Result.Success@tok () Term)
(declare-fun FStar.Tactics.Result.Failed (Term Term Term) Term)
(declare-fun FStar.Tactics.Result.Failed_a (Term) Term)
(declare-fun FStar.Tactics.Result.Failed_exn (Term) Term)
(declare-fun FStar.Tactics.Result.Failed_ps (Term) Term)
(declare-fun FStar.Tactics.Result.Failed@tok () Term)
(define-fun
  is-FStar.Tactics.Result.__result
  ((__@x0 Term))
  Bool
  (and
    (= (Term_constr_id __@x0) 101)
    (exists ((@x0 Term)) (= __@x0 (FStar.Tactics.Result.__result @x0)))))
(assert
  (forall
    ((@x0 Term) (@x1 Term) (@x2 Term))
    (!
      (= 108 (Term_constr_id (FStar.Tactics.Result.Success @x0 @x1 @x2)))
      :pattern
      ((FStar.Tactics.Result.Success @x0 @x1 @x2)))))

(assert
  (forall
    ((@x0 Term) (@x1 Term) (@x2 Term))
    (!
      (=
        (FStar.Tactics.Result.Success_a
          (FStar.Tactics.Result.Success @x0 @x1 @x2))
        @x0)
      :pattern
      ((FStar.Tactics.Result.Success @x0 @x1 @x2)))))

(assert
  (forall
    ((@x0 Term) (@x1 Term) (@x2 Term))
    (!
      (=
        (FStar.Tactics.Result.Success_v
          (FStar.Tactics.Result.Success @x0 @x1 @x2))
        @x1)
      :pattern
      ((FStar.Tactics.Result.Success @x0 @x1 @x2)))))

(assert
  (forall
    ((@x0 Term) (@x1 Term) (@x2 Term))
    (!
      (=
        (FStar.Tactics.Result.Success_ps
          (FStar.Tactics.Result.Success @x0 @x1 @x2))
        @x2)
      :pattern
      ((FStar.Tactics.Result.Success @x0 @x1 @x2)))))

(define-fun
  is-FStar.Tactics.Result.Success
  ((__@x0 Term))
  Bool
  (and
    (= (Term_constr_id __@x0) 108)
    (=
      __@x0
      (FStar.Tactics.Result.Success
        (FStar.Tactics.Result.Success_a __@x0)
        (FStar.Tactics.Result.Success_v __@x0)
        (FStar.Tactics.Result.Success_ps __@x0)))))

(assert
  (forall
    ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
    (!
      (implies
        (HasTypeFuel
          (SFuel @u0)
          (FStar.Tactics.Result.Success @x1 @x2 @x3)
          (FStar.Tactics.Result.__result @x4))
        (and
          (HasTypeFuel @u0 @x4 Tm_type)
          (HasTypeFuel @u0 @x2 @x4)
          (HasTypeFuel @u0 @x1 Tm_type)
          (HasTypeFuel @u0 @x2 @x1)
          (HasTypeFuel @u0 @x3 FStar.Tactics.Types.proofstate)))
      :pattern
      (
        (HasTypeFuel
          (SFuel @u0)
          (FStar.Tactics.Result.Success @x1 @x2 @x3)
          (FStar.Tactics.Result.__result @x4))))))

(assert
  (forall
    ((@x0 Term) (@x1 Term) (@x2 Term))
    (!
      (= 113 (Term_constr_id (FStar.Tactics.Result.Failed @x0 @x1 @x2)))
      :pattern
      ((FStar.Tactics.Result.Failed @x0 @x1 @x2)))))

(define-fun
  is-FStar.Tactics.Result.Failed
  ((__@x0 Term))
  Bool
  (and
    (= (Term_constr_id __@x0) 113)
    (=
      __@x0
      (FStar.Tactics.Result.Failed
        (FStar.Tactics.Result.Failed_a __@x0)
        (FStar.Tactics.Result.Failed_exn __@x0)
        (FStar.Tactics.Result.Failed_ps __@x0)))))

(assert
  (forall
    ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term))
    (!
      (implies
        (and
          (HasTypeFuel @u0 @x1 Tm_type)
          (HasTypeFuel @u0 @x2 Prims.exn)
          (HasTypeFuel @u0 @x3 FStar.Tactics.Types.proofstate))
        (HasTypeFuel
          @u0
          (FStar.Tactics.Result.Failed @x1 @x2 @x3)
          (FStar.Tactics.Result.__result @x1)))
      :pattern
      (
        (HasTypeFuel
          @u0
          (FStar.Tactics.Result.Failed @x1 @x2 @x3)
          (FStar.Tactics.Result.__result @x1))))))

(assert
  (!
    (forall
      ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term) (@x4 Term))
      (!
        (implies
          (HasTypeFuel
            (SFuel @u0)
            (FStar.Tactics.Result.Failed @x1 @x2 @x3)
            (FStar.Tactics.Result.__result @x4))
          (and
            (HasTypeFuel @u0 @x4 Tm_type)
            (HasTypeFuel @u0 @x1 Tm_type)
            (HasTypeFuel @u0 @x2 Prims.exn)
            (HasTypeFuel @u0 @x3 FStar.Tactics.Types.proofstate)))
        :pattern
        (
          (HasTypeFuel
            (SFuel @u0)
            (FStar.Tactics.Result.Failed @x1 @x2 @x3)
            (FStar.Tactics.Result.__result @x4)))))))

(assert
  (forall
    ((@u0 Fuel) (@x1 Term) (@x2 Term))
    (!
      (implies
        (HasTypeFuel (SFuel @u0) @x1 (FStar.Tactics.Result.__result @x2))
        (or
          (and
            (is-FStar.Tactics.Result.Success @x1)
            (= @x2 (FStar.Tactics.Result.Success_a @x1)))
          (and
            (is-FStar.Tactics.Result.Failed @x1)
            (= @x2 (FStar.Tactics.Result.Failed_a @x1)))))
      :pattern
      ((HasTypeFuel (SFuel @u0) @x1 (FStar.Tactics.Result.__result @x2))))))

(declare-fun label_9 () Bool)
(declare-fun label_8 () Bool)
(declare-fun label_7 () Bool)
(declare-fun label_6 () Bool)
(declare-fun label_5 () Bool)
(declare-fun label_4 () Bool)
(declare-fun label_3 () Bool)
(declare-fun label_2 () Bool)
(declare-fun label_1 () Bool)
(declare-fun Non_total_Tm_arrow_01a667a9d658d9870ab8a6e6c8402f2a () Term)
(declare-fun Tm_arrow_b8e144d0da1e757197d5cbec0bbcc261 () Term)
(assert
  (forall
    ((@x0 Term))
    (!
      (iff
        (HasTypeZ @x0 Tm_arrow_b8e144d0da1e757197d5cbec0bbcc261)
        (forall
          ((@x1 Term))
          (!
            (implies
              (HasType @x1 (FStar.Tactics.Result.__result Prims.int))
              (HasType (ApplyTT @x0 @x1) Tm_type))
            :pattern
            ((ApplyTT @x0 @x1)))))
      :pattern
      ((HasTypeZ @x0 Tm_arrow_b8e144d0da1e757197d5cbec0bbcc261)))))

(assert (! (= MaxIFuel (SFuel ZFuel)) :named @MaxIFuel_assumption))

(assert
  (not
    (forall
      ((@x0 Term))
      (implies
        (HasType @x0 Non_total_Tm_arrow_01a667a9d658d9870ab8a6e6c8402f2a)
        (forall
          ((@x1 Term) (@x2 Term))
          (!
            (implies
              (and
                (HasType @x1 FStar.Tactics.Types.proofstate)
                (HasType @x2 Tm_arrow_b8e144d0da1e757197d5cbec0bbcc261)
                (forall
                  ((@x3 Term))
                  (!
                    (implies
                      (let
                        ((@lb4 @x3))
                        (ite
                          (is-FStar.Tactics.Result.Success @lb4)
                          (forall
                            ((@x5 Term))
                            (!
                              (implies
                                (and
                                  (HasType
                                    @x5
                                    Tm_arrow_b8e144d0da1e757197d5cbec0bbcc261)
                                  (forall
                                    ((@x6 Term))
                                    (!
                                      (implies
                                        (let
                                          ((@lb7 @x6))
                                          (ite
                                            (is-FStar.Tactics.Result.Success
                                              @lb7)
                                            (forall
                                              ((@x8 Term))
                                              (!
                                                (implies
                                                  (and
                                                    (HasType
                                                      @x8
                                                      Tm_arrow_b8e144d0da1e757197d5cbec0bbcc261)
                                                    (forall
                                                      ((@x9 Term))
                                                      (!
                                                        (implies
                                                          (let
                                                            ((@lb10 @x9))
                                                            (ite
                                                              (is-FStar.Tactics.Result.Success
                                                                @lb10)
                                                              (forall
                                                                ((@x11 Term))
                                                                (!
                                                                  (implies
                                                                    (and
                                                                      (HasType
                                                                        @x11
                                                                        Tm_arrow_b8e144d0da1e757197d5cbec0bbcc261)
                                                                      (forall
                                                                        (
                                                                          (@x12 Term))
                                                                        (!
                                                                          (implies
                                                                            (let
                                                                              (
                                                                                (@lb13 @x12))
                                                                              (ite
                                                                                (is-FStar.Tactics.Result.Success
                                                                                  @lb13)
                                                                                (forall
                                                                                  (
                                                                                    (@x14 Term))
                                                                                  (!
                                                                                    (implies
                                                                                      (and
                                                                                        (HasType
                                                                                          @x14
                                                                                          Tm_arrow_b8e144d0da1e757197d5cbec0bbcc261)
                                                                                        (forall
                                                                                          (
                                                                                            (@x15 Term))
                                                                                          (!
                                                                                            (implies
                                                                                              (let
                                                                                                (
                                                                                                  (@lb16 @x15))
                                                                                                (ite
                                                                                                  (is-FStar.Tactics.Result.Success
                                                                                                    @lb16)
                                                                                                  (forall
                                                                                                    (
                                                                                                      (@x17 Term))
                                                                                                    (!
                                                                                                      (implies
                                                                                                        (and
                                                                                                          (HasType
                                                                                                            @x17
                                                                                                            Tm_arrow_b8e144d0da1e757197d5cbec0bbcc261)
                                                                                                          (forall
                                                                                                            (
                                                                                                              (@x18 Term))
                                                                                                            (!
                                                                                                              (implies
                                                                                                                (let
                                                                                                                  (
                                                                                                                    (@lb19 @x18))
                                                                                                                  (ite
                                                                                                                    (is-FStar.Tactics.Result.Success
                                                                                                                      @lb19)
                                                                                                                    (forall
                                                                                                                      (
                                                                                                                        (@x20 Term))
                                                                                                                      (!
                                                                                                                        (implies
                                                                                                                          (and
                                                                                                                            (HasType
                                                                                                                              @x20
                                                                                                                              Tm_arrow_b8e144d0da1e757197d5cbec0bbcc261)
                                                                                                                            (forall
                                                                                                                              (
                                                                                                                                (@x21 Term))
                                                                                                                              (!
                                                                                                                                (implies
                                                                                                                                  (let
                                                                                                                                    (
                                                                                                                                      (@lb22 @x21))
                                                                                                                                    (ite
                                                                                                                                      (is-FStar.Tactics.Result.Success
                                                                                                                                        @lb22)
                                                                                                                                      (forall
                                                                                                                                        (
                                                                                                                                          (@x23 Term))
                                                                                                                                        (!
                                                                                                                                          (implies
                                                                                                                                            (and
                                                                                                                                              (HasType
                                                                                                                                                @x23
                                                                                                                                                Tm_arrow_b8e144d0da1e757197d5cbec0bbcc261)
                                                                                                                                              (forall
                                                                                                                                                (
                                                                                                                                                  (@x24 Term))
                                                                                                                                                (!
                                                                                                                                                  (implies
                                                                                                                                                    (let
                                                                                                                                                      (
                                                                                                                                                        (@lb25 @x24))
                                                                                                                                                      (ite
                                                                                                                                                        (is-FStar.Tactics.Result.Success
                                                                                                                                                          @lb25)
                                                                                                                                                        (forall
                                                                                                                                                          (
                                                                                                                                                            (@x26 Term))
                                                                                                                                                          (!
                                                                                                                                                            (implies
                                                                                                                                                              (HasType
                                                                                                                                                                @x26
                                                                                                                                                                (FStar.Tactics.Result.__result (FStar.Pervasives.Native.option Prims.int)))
                                                                                                                                                              (let
                                                                                                                                                                (
                                                                                                                                                                  (@lb27 @x26))
                                                                                                                                                                (ite
                                                                                                                                                                  (is-FStar.Tactics.Result.Success
                                                                                                                                                                    @lb27)
                                                                                                                                                                  (implies
                                                                                                                                                                    (and
                                                                                                                                                                      (not
                                                                                                                                                                        (BoxBool_proj_0
                                                                                                                                                                          (FStar.Pervasives.Native.uu___is_Some
                                                                                                                                                                            Prims.int
                                                                                                                                                                            (FStar.Tactics.Result.Success_v @lb27))))
                                                                                                                                                                      (not
                                                                                                                                                                        (BoxBool_proj_0
                                                                                                                                                                          (FStar.Pervasives.Native.uu___is_None
                                                                                                                                                                            Prims.int
                                                                                                                                                                            (FStar.Tactics.Result.Success_v @lb27)))))
                                                                                                                                                                    label_1)
                                                                                                                                                                  (is-FStar.Tactics.Result.Failed @lb27))))))
                                                                                                                                                        (is-FStar.Tactics.Result.Failed @lb25)))
                                                                                                                                                    (Valid (ApplyTT @x23 @x24)))
                                                                                                                                                  :pattern
                                                                                                                                                  ((ApplyTT @x23 @x24)))))
                                                                                                                                            (forall
                                                                                                                                              (
                                                                                                                                                (@x24 Term))
                                                                                                                                              (!
                                                                                                                                                (implies
                                                                                                                                                  (HasType
                                                                                                                                                    @x24
                                                                                                                                                    (FStar.Tactics.Result.__result (FStar.Pervasives.Native.option Prims.int)))
                                                                                                                                                  (let
                                                                                                                                                    (
                                                                                                                                                      (@lb25 @x24))
                                                                                                                                                    (ite
                                                                                                                                                      (is-FStar.Tactics.Result.Success
                                                                                                                                                        @lb25)
                                                                                                                                                      (forall
                                                                                                                                                        (
                                                                                                                                                          (@x26 Term))
                                                                                                                                                        (!
                                                                                                                                                          (implies
                                                                                                                                                            (and
                                                                                                                                                              (HasType
                                                                                                                                                                @x26
                                                                                                                                                                Tm_arrow_b8e144d0da1e757197d5cbec0bbcc261)
                                                                                                                                                              (forall
                                                                                                                                                                (
                                                                                                                                                                  (@x27 Term))
                                                                                                                                                                (!
                                                                                                                                                                  (implies
                                                                                                                                                                    (Valid
                                                                                                                                                                      (ApplyTT @x23 @x27))
                                                                                                                                                                    (Valid (ApplyTT @x26 @x27)))
                                                                                                                                                                  :weight
                                                                                                                                                                  0
                                                                                                                                                                  :pattern
                                                                                                                                                                  ((ApplyTT @x26 @x27)))))
                                                                                                                                                            (forall
                                                                                                                                                              (
                                                                                                                                                                (@x27 Term))
                                                                                                                                                              (!
                                                                                                                                                                (implies
                                                                                                                                                                  (and
                                                                                                                                                                    (HasType
                                                                                                                                                                      @x27
                                                                                                                                                                      (Prims.pure_post Prims.int))
                                                                                                                                                                    (forall
                                                                                                                                                                      (
                                                                                                                                                                        (@x28 Term))
                                                                                                                                                                      (!
                                                                                                                                                                        (implies
                                                                                                                                                                          (forall
                                                                                                                                                                            (
                                                                                                                                                                              (@x29 Term))
                                                                                                                                                                            (!
                                                                                                                                                                              (implies
                                                                                                                                                                                (and
                                                                                                                                                                                  (HasType
                                                                                                                                                                                    @x29
                                                                                                                                                                                    Tm_arrow_b8e144d0da1e757197d5cbec0bbcc261)
                                                                                                                                                                                  (forall
                                                                                                                                                                                    (
                                                                                                                                                                                      (@x30 Term))
                                                                                                                                                                                    (!
                                                                                                                                                                                      (implies
                                                                                                                                                                                        (Valid
                                                                                                                                                                                          (ApplyTT @x26 @x30))
                                                                                                                                                                                        (Valid (ApplyTT @x29 @x30)))
                                                                                                                                                                                      :pattern
                                                                                                                                                                                      ((ApplyTT @x29 @x30))))
                                                                                                                                                                                  (=
                                                                                                                                                                                    @x28
                                                                                                                                                                                    (let
                                                                                                                                                                                      (
                                                                                                                                                                                        (@lb30 (FStar.Tactics.Result.Success_v @lb25)))
                                                                                                                                                                                      (ite
                                                                                                                                                                                        (is-FStar.Pervasives.Native.Some
                                                                                                                                                                                          @lb30)
                                                                                                                                                                                        (FStar.Pervasives.Native.Some_v
                                                                                                                                                                                          @lb30)
                                                                                                                                                                                        (ite (is-FStar.Pervasives.Native.None @lb30) (BoxInt 0) Tm_unit)))))
                                                                                                                                                                                (Valid
                                                                                                                                                                                  (ApplyTT
                                                                                                                                                                                    @x29
                                                                                                                                                                                    (FStar.Tactics.Result.Success
                                                                                                                                                                                      Prims.int
                                                                                                                                                                                      @x28
                                                                                                                                                                                      (FStar.Tactics.Result.Success_ps @lb25)))))))
                                                                                                                                                                          (Valid (ApplyTT @x27 @x28)))
                                                                                                                                                                        :pattern
                                                                                                                                                                        ((ApplyTT @x27 @x28)))))
                                                                                                                                                                  (and
                                                                                                                                                                    (implies
                                                                                                                                                                      (and
                                                                                                                                                                        (not
                                                                                                                                                                          (BoxBool_proj_0
                                                                                                                                                                            (FStar.Pervasives.Native.uu___is_Some
                                                                                                                                                                              Prims.int
                                                                                                                                                                              (FStar.Tactics.Result.Success_v @lb25))))
                                                                                                                                                                        (not
                                                                                                                                                                          (BoxBool_proj_0
                                                                                                                                                                            (FStar.Pervasives.Native.uu___is_None
                                                                                                                                                                              Prims.int
                                                                                                                                                                              (FStar.Tactics.Result.Success_v @lb25)))))
                                                                                                                                                                      label_2)
                                                                                                                                                                    (forall
                                                                                                                                                                      (
                                                                                                                                                                        (@x28 Term))
                                                                                                                                                                      (!
                                                                                                                                                                        (implies
                                                                                                                                                                          (and
                                                                                                                                                                            (HasType
                                                                                                                                                                              @x28
                                                                                                                                                                              Prims.int)
                                                                                                                                                                            (=
                                                                                                                                                                              (FStar.Tactics.Result.Success_v
                                                                                                                                                                                @lb25)
                                                                                                                                                                              (FStar.Pervasives.Native.Some Prims.int @x28)))
                                                                                                                                                                          (forall
                                                                                                                                                                            (
                                                                                                                                                                              (@x29 Term))
                                                                                                                                                                            (! (implies (HasType @x29 Prims.int) (Valid (ApplyTT @x27 @x29))))))))
                                                                                                                                                                    (implies
                                                                                                                                                                      (and
                                                                                                                                                                        (not
                                                                                                                                                                          (BoxBool_proj_0
                                                                                                                                                                            (FStar.Pervasives.Native.uu___is_Some
                                                                                                                                                                              Prims.int
                                                                                                                                                                              (FStar.Tactics.Result.Success_v @lb25))))
                                                                                                                                                                        (=
                                                                                                                                                                          (FStar.Tactics.Result.Success_v
                                                                                                                                                                            @lb25)
                                                                                                                                                                          (FStar.Pervasives.Native.None Prims.int)))
                                                                                                                                                                      (forall
                                                                                                                                                                        (
                                                                                                                                                                          (@x28 Term))
                                                                                                                                                                        (! (implies (HasType @x28 Prims.int) (Valid (ApplyTT @x27 @x28)))))))))))))
                                                                                                                                                      (implies
                                                                                                                                                        (is-FStar.Tactics.Result.Failed
                                                                                                                                                          @lb25)
                                                                                                                                                        (Valid
                                                                                                                                                          (ApplyTT
                                                                                                                                                            @x23
                                                                                                                                                            (FStar.Tactics.Result.Failed
                                                                                                                                                              Prims.int
                                                                                                                                                              (FStar.Tactics.Result.Failed_exn
                                                                                                                                                                @lb25)
                                                                                                                                                              (FStar.Tactics.Result.Failed_ps @lb25)))))))))))))
                                                                                                                                      (is-FStar.Tactics.Result.Failed @lb22)))
                                                                                                                                  (Valid (ApplyTT @x20 @x21)))
                                                                                                                                :pattern
                                                                                                                                ((ApplyTT @x20 @x21)))))
                                                                                                                          (forall
                                                                                                                            (
                                                                                                                              (@x21 Term))
                                                                                                                            (!
                                                                                                                              (implies
                                                                                                                                (HasType
                                                                                                                                  @x21
                                                                                                                                  (FStar.Tactics.Result.__result (FStar.Pervasives.Native.option Prims.int)))
                                                                                                                                (let
                                                                                                                                  (
                                                                                                                                    (@lb22 @x21))
                                                                                                                                  (ite
                                                                                                                                    (is-FStar.Tactics.Result.Success
                                                                                                                                      @lb22)
                                                                                                                                    (forall
                                                                                                                                      (
                                                                                                                                        (@x23 Term))
                                                                                                                                      (!
                                                                                                                                        (implies
                                                                                                                                          (and
                                                                                                                                            (HasType
                                                                                                                                              @x23
                                                                                                                                              Tm_arrow_b8e144d0da1e757197d5cbec0bbcc261)
                                                                                                                                            (forall
                                                                                                                                              (
                                                                                                                                                (@x24 Term))
                                                                                                                                              (!
                                                                                                                                                (implies
                                                                                                                                                  (Valid
                                                                                                                                                    (ApplyTT @x20 @x24))
                                                                                                                                                  (Valid (ApplyTT @x23 @x24)))
                                                                                                                                                :pattern
                                                                                                                                                ((ApplyTT @x23 @x24)))))
                                                                                                                                          (forall
                                                                                                                                            (
                                                                                                                                              (@x24 Term))
                                                                                                                                            (!
                                                                                                                                              (implies
                                                                                                                                                (and
                                                                                                                                                  (HasType
                                                                                                                                                    @x24
                                                                                                                                                    (Prims.pure_post Prims.int))
                                                                                                                                                  (forall
                                                                                                                                                    (
                                                                                                                                                      (@x25 Term))
                                                                                                                                                    (!
                                                                                                                                                      (implies
                                                                                                                                                        (forall
                                                                                                                                                          (
                                                                                                                                                            (@x26 Term))
                                                                                                                                                          (!
                                                                                                                                                            (implies
                                                                                                                                                              (and
                                                                                                                                                                (HasType
                                                                                                                                                                  @x26
                                                                                                                                                                  Tm_arrow_b8e144d0da1e757197d5cbec0bbcc261)
                                                                                                                                                                (forall
                                                                                                                                                                  (
                                                                                                                                                                    (@x27 Term))
                                                                                                                                                                  (!
                                                                                                                                                                    (implies
                                                                                                                                                                      (Valid
                                                                                                                                                                        (ApplyTT @x23 @x27))
                                                                                                                                                                      (Valid (ApplyTT @x26 @x27)))
                                                                                                                                                                    :pattern
                                                                                                                                                                    ((ApplyTT @x26 @x27))))
                                                                                                                                                                (=
                                                                                                                                                                  @x25
                                                                                                                                                                  (let
                                                                                                                                                                    (
                                                                                                                                                                      (@lb27 (FStar.Tactics.Result.Success_v @lb22)))
                                                                                                                                                                    (ite
                                                                                                                                                                      (is-FStar.Pervasives.Native.Some
                                                                                                                                                                        @lb27)
                                                                                                                                                                      (FStar.Pervasives.Native.Some_v
                                                                                                                                                                        @lb27)
                                                                                                                                                                      (ite (is-FStar.Pervasives.Native.None @lb27) (BoxInt 0) Tm_unit)))))
                                                                                                                                                              (Valid
                                                                                                                                                                (ApplyTT
                                                                                                                                                                  @x26
                                                                                                                                                                  (FStar.Tactics.Result.Success
                                                                                                                                                                    Prims.int
                                                                                                                                                                    @x25
                                                                                                                                                                    (FStar.Tactics.Result.Success_ps @lb22)))))))
                                                                                                                                                        (Valid (ApplyTT @x24 @x25)))
                                                                                                                                                      :pattern
                                                                                                                                                      ((ApplyTT @x24 @x25)))))
                                                                                                                                                (and
                                                                                                                                                  (implies
                                                                                                                                                    (and
                                                                                                                                                      (not
                                                                                                                                                        (BoxBool_proj_0
                                                                                                                                                          (FStar.Pervasives.Native.uu___is_Some
                                                                                                                                                            Prims.int
                                                                                                                                                            (FStar.Tactics.Result.Success_v @lb22))))
                                                                                                                                                      (not
                                                                                                                                                        (BoxBool_proj_0
                                                                                                                                                          (FStar.Pervasives.Native.uu___is_None
                                                                                                                                                            Prims.int
                                                                                                                                                            (FStar.Tactics.Result.Success_v @lb22)))))
                                                                                                                                                    label_3)
                                                                                                                                                  (forall
                                                                                                                                                    (
                                                                                                                                                      (@x25 Term))
                                                                                                                                                    (!
                                                                                                                                                      (implies
                                                                                                                                                        (and
                                                                                                                                                          (HasType
                                                                                                                                                            @x25
                                                                                                                                                            Prims.int)
                                                                                                                                                          (=
                                                                                                                                                            (FStar.Tactics.Result.Success_v
                                                                                                                                                              @lb22)
                                                                                                                                                            (FStar.Pervasives.Native.Some Prims.int @x25)))
                                                                                                                                                        (forall
                                                                                                                                                          (
                                                                                                                                                            (@x26 Term))
                                                                                                                                                          (! (implies (HasType @x26 Prims.int) (Valid (ApplyTT @x24 @x26))))))))
                                                                                                                                                  (implies
                                                                                                                                                    (and
                                                                                                                                                      (not
                                                                                                                                                        (BoxBool_proj_0
                                                                                                                                                          (FStar.Pervasives.Native.uu___is_Some
                                                                                                                                                            Prims.int
                                                                                                                                                            (FStar.Tactics.Result.Success_v @lb22))))
                                                                                                                                                      (=
                                                                                                                                                        (FStar.Tactics.Result.Success_v
                                                                                                                                                          @lb22)
                                                                                                                                                        (FStar.Pervasives.Native.None Prims.int)))
                                                                                                                                                    (forall
                                                                                                                                                      (
                                                                                                                                                        (@x25 Term))
                                                                                                                                                      (! (implies (HasType @x25 Prims.int) (Valid (ApplyTT @x24 @x25)))))))))))))
                                                                                                                                    (implies
                                                                                                                                      (is-FStar.Tactics.Result.Failed
                                                                                                                                        @lb22)
                                                                                                                                      (Valid
                                                                                                                                        (ApplyTT
                                                                                                                                          @x20
                                                                                                                                          (FStar.Tactics.Result.Failed
                                                                                                                                            Prims.int
                                                                                                                                            (FStar.Tactics.Result.Failed_exn
                                                                                                                                              @lb22)
                                                                                                                                            (FStar.Tactics.Result.Failed_ps @lb22)))))))))))))
                                                                                                                    (is-FStar.Tactics.Result.Failed @lb19)))
                                                                                                                (Valid (ApplyTT @x17 @x18)))
                                                                                                              :pattern
                                                                                                              ((ApplyTT @x17 @x18)))))
                                                                                                        (forall
                                                                                                          (
                                                                                                            (@x18 Term))
                                                                                                          (!
                                                                                                            (implies
                                                                                                              (HasType
                                                                                                                @x18
                                                                                                                (FStar.Tactics.Result.__result (FStar.Pervasives.Native.option Prims.int)))
                                                                                                              (let
                                                                                                                (
                                                                                                                  (@lb19 @x18))
                                                                                                                (ite
                                                                                                                  (is-FStar.Tactics.Result.Success
                                                                                                                    @lb19)
                                                                                                                  (forall
                                                                                                                    (
                                                                                                                      (@x20 Term))
                                                                                                                    (!
                                                                                                                      (implies
                                                                                                                        (and
                                                                                                                          (HasType
                                                                                                                            @x20
                                                                                                                            Tm_arrow_b8e144d0da1e757197d5cbec0bbcc261)
                                                                                                                          (forall
                                                                                                                            (
                                                                                                                              (@x21 Term))
                                                                                                                            (!
                                                                                                                              (implies
                                                                                                                                (Valid
                                                                                                                                  (ApplyTT @x17 @x21))
                                                                                                                                (Valid (ApplyTT @x20 @x21)))
                                                                                                                              :pattern
                                                                                                                              ((ApplyTT @x20 @x21)))))
                                                                                                                        (forall
                                                                                                                          (
                                                                                                                            (@x21 Term))
                                                                                                                          (!
                                                                                                                            (implies
                                                                                                                              (and
                                                                                                                                (HasType
                                                                                                                                  @x21
                                                                                                                                  (Prims.pure_post Prims.int))
                                                                                                                                (forall
                                                                                                                                  (
                                                                                                                                    (@x22 Term))
                                                                                                                                  (!
                                                                                                                                    (implies
                                                                                                                                      (forall
                                                                                                                                        (
                                                                                                                                          (@x23 Term))
                                                                                                                                        (!
                                                                                                                                          (implies
                                                                                                                                            (and
                                                                                                                                              (HasType
                                                                                                                                                @x23
                                                                                                                                                Tm_arrow_b8e144d0da1e757197d5cbec0bbcc261)
                                                                                                                                              (forall
                                                                                                                                                (
                                                                                                                                                  (@x24 Term))
                                                                                                                                                (!
                                                                                                                                                  (implies
                                                                                                                                                    (Valid
                                                                                                                                                      (ApplyTT @x20 @x24))
                                                                                                                                                    (Valid (ApplyTT @x23 @x24)))
                                                                                                                                                  :pattern
                                                                                                                                                  ((ApplyTT @x23 @x24))))
                                                                                                                                              (=
                                                                                                                                                @x22
                                                                                                                                                (let
                                                                                                                                                  (
                                                                                                                                                    (@lb24 (FStar.Tactics.Result.Success_v @lb19)))
                                                                                                                                                  (ite
                                                                                                                                                    (is-FStar.Pervasives.Native.Some
                                                                                                                                                      @lb24)
                                                                                                                                                    (FStar.Pervasives.Native.Some_v
                                                                                                                                                      @lb24)
                                                                                                                                                    (ite (is-FStar.Pervasives.Native.None @lb24) (BoxInt 0) Tm_unit)))))
                                                                                                                                            (Valid
                                                                                                                                              (ApplyTT
                                                                                                                                                @x23
                                                                                                                                                (FStar.Tactics.Result.Success
                                                                                                                                                  Prims.int
                                                                                                                                                  @x22
                                                                                                                                                  (FStar.Tactics.Result.Success_ps @lb19)))))))
                                                                                                                                      (Valid (ApplyTT @x21 @x22)))
                                                                                                                                    :pattern
                                                                                                                                    ((ApplyTT @x21 @x22)))))
                                                                                                                              (and
                                                                                                                                (implies
                                                                                                                                  (and
                                                                                                                                    (not
                                                                                                                                      (BoxBool_proj_0
                                                                                                                                        (FStar.Pervasives.Native.uu___is_Some
                                                                                                                                          Prims.int
                                                                                                                                          (FStar.Tactics.Result.Success_v @lb19))))
                                                                                                                                    (not
                                                                                                                                      (BoxBool_proj_0
                                                                                                                                        (FStar.Pervasives.Native.uu___is_None
                                                                                                                                          Prims.int
                                                                                                                                          (FStar.Tactics.Result.Success_v @lb19)))))
                                                                                                                                  label_4)
                                                                                                                                (forall
                                                                                                                                  (
                                                                                                                                    (@x22 Term))
                                                                                                                                  (!
                                                                                                                                    (implies
                                                                                                                                      (and
                                                                                                                                        (HasType
                                                                                                                                          @x22
                                                                                                                                          Prims.int)
                                                                                                                                        (=
                                                                                                                                          (FStar.Tactics.Result.Success_v
                                                                                                                                            @lb19)
                                                                                                                                          (FStar.Pervasives.Native.Some Prims.int @x22)))
                                                                                                                                      (forall
                                                                                                                                        (
                                                                                                                                          (@x23 Term))
                                                                                                                                        (! (implies (HasType @x23 Prims.int) (Valid (ApplyTT @x21 @x23))))))))
                                                                                                                                (implies
                                                                                                                                  (and
                                                                                                                                    (not
                                                                                                                                      (BoxBool_proj_0
                                                                                                                                        (FStar.Pervasives.Native.uu___is_Some
                                                                                                                                          Prims.int
                                                                                                                                          (FStar.Tactics.Result.Success_v @lb19))))
                                                                                                                                    (=
                                                                                                                                      (FStar.Tactics.Result.Success_v
                                                                                                                                        @lb19)
                                                                                                                                      (FStar.Pervasives.Native.None Prims.int)))
                                                                                                                                  (forall
                                                                                                                                    (
                                                                                                                                      (@x22 Term))
                                                                                                                                    (! (implies (HasType @x22 Prims.int) (Valid (ApplyTT @x21 @x22)))))))))))))
                                                                                                                  (implies
                                                                                                                    (is-FStar.Tactics.Result.Failed
                                                                                                                      @lb19)
                                                                                                                    (Valid
                                                                                                                      (ApplyTT
                                                                                                                        @x17
                                                                                                                        (FStar.Tactics.Result.Failed
                                                                                                                          Prims.int
                                                                                                                          (FStar.Tactics.Result.Failed_exn
                                                                                                                            @lb19)
                                                                                                                          (FStar.Tactics.Result.Failed_ps @lb19)))))))))))))
                                                                                                  (is-FStar.Tactics.Result.Failed @lb16)))
                                                                                              (Valid (ApplyTT @x14 @x15)))
                                                                                            :pattern
                                                                                            ((ApplyTT @x14 @x15)))))
                                                                                      (forall
                                                                                        (
                                                                                          (@x15 Term))
                                                                                        (!
                                                                                          (implies
                                                                                            (HasType
                                                                                              @x15
                                                                                              (FStar.Tactics.Result.__result (FStar.Pervasives.Native.option Prims.int)))
                                                                                            (let
                                                                                              (
                                                                                                (@lb16 @x15))
                                                                                              (ite
                                                                                                (is-FStar.Tactics.Result.Success
                                                                                                  @lb16)
                                                                                                (forall
                                                                                                  (
                                                                                                    (@x17 Term))
                                                                                                  (!
                                                                                                    (implies
                                                                                                      (and
                                                                                                        (HasType
                                                                                                          @x17
                                                                                                          Tm_arrow_b8e144d0da1e757197d5cbec0bbcc261)
                                                                                                        (forall
                                                                                                          (
                                                                                                            (@x18 Term))
                                                                                                          (!
                                                                                                            (implies
                                                                                                              (Valid
                                                                                                                (ApplyTT @x14 @x18))
                                                                                                              (Valid (ApplyTT @x17 @x18)))
                                                                                                            :pattern
                                                                                                            ((ApplyTT @x17 @x18)))))
                                                                                                      (forall
                                                                                                        (
                                                                                                          (@x18 Term))
                                                                                                        (!
                                                                                                          (implies
                                                                                                            (and
                                                                                                              (HasType
                                                                                                                @x18
                                                                                                                (Prims.pure_post Prims.int))
                                                                                                              (forall
                                                                                                                (
                                                                                                                  (@x19 Term))
                                                                                                                (!
                                                                                                                  (implies
                                                                                                                    (forall
                                                                                                                      (
                                                                                                                        (@x20 Term))
                                                                                                                      (!
                                                                                                                        (implies
                                                                                                                          (and
                                                                                                                            (HasType
                                                                                                                              @x20
                                                                                                                              Tm_arrow_b8e144d0da1e757197d5cbec0bbcc261)
                                                                                                                            (forall
                                                                                                                              (
                                                                                                                                (@x21 Term))
                                                                                                                              (!
                                                                                                                                (implies
                                                                                                                                  (Valid
                                                                                                                                    (ApplyTT @x17 @x21))
                                                                                                                                  (Valid (ApplyTT @x20 @x21)))
                                                                                                                                :weight
                                                                                                                                0
                                                                                                                                :pattern
                                                                                                                                ((ApplyTT @x20 @x21))))
                                                                                                                            (=
                                                                                                                              @x19
                                                                                                                              (let
                                                                                                                                (
                                                                                                                                  (@lb21 (FStar.Tactics.Result.Success_v @lb16)))
                                                                                                                                (ite
                                                                                                                                  (is-FStar.Pervasives.Native.Some
                                                                                                                                    @lb21)
                                                                                                                                  (FStar.Pervasives.Native.Some_v
                                                                                                                                    @lb21)
                                                                                                                                  (ite (is-FStar.Pervasives.Native.None @lb21) (BoxInt 0) Tm_unit)))))
                                                                                                                          (Valid
                                                                                                                            (ApplyTT
                                                                                                                              @x20
                                                                                                                              (FStar.Tactics.Result.Success
                                                                                                                                Prims.int
                                                                                                                                @x19
                                                                                                                                (FStar.Tactics.Result.Success_ps @lb16)))))))
                                                                                                                    (Valid (ApplyTT @x18 @x19)))
                                                                                                                  :weight
                                                                                                                  0
                                                                                                                  :pattern
                                                                                                                  ((ApplyTT @x18 @x19)))))
                                                                                                            (and
                                                                                                              (implies
                                                                                                                (and
                                                                                                                  (not
                                                                                                                    (BoxBool_proj_0
                                                                                                                      (FStar.Pervasives.Native.uu___is_Some
                                                                                                                        Prims.int
                                                                                                                        (FStar.Tactics.Result.Success_v @lb16))))
                                                                                                                  (not
                                                                                                                    (BoxBool_proj_0
                                                                                                                      (FStar.Pervasives.Native.uu___is_None
                                                                                                                        Prims.int
                                                                                                                        (FStar.Tactics.Result.Success_v @lb16)))))
                                                                                                                label_5)
                                                                                                              (forall
                                                                                                                (
                                                                                                                  (@x19 Term))
                                                                                                                (!
                                                                                                                  (implies
                                                                                                                    (and
                                                                                                                      (HasType
                                                                                                                        @x19
                                                                                                                        Prims.int)
                                                                                                                      (=
                                                                                                                        (FStar.Tactics.Result.Success_v
                                                                                                                          @lb16)
                                                                                                                        (FStar.Pervasives.Native.Some Prims.int @x19)))
                                                                                                                    (forall
                                                                                                                      (
                                                                                                                        (@x20 Term))
                                                                                                                      (! (implies (HasType @x20 Prims.int) (Valid (ApplyTT @x18 @x20))))))))
                                                                                                              (implies
                                                                                                                (and
                                                                                                                  (not
                                                                                                                    (BoxBool_proj_0
                                                                                                                      (FStar.Pervasives.Native.uu___is_Some
                                                                                                                        Prims.int
                                                                                                                        (FStar.Tactics.Result.Success_v @lb16))))
                                                                                                                  (=
                                                                                                                    (FStar.Tactics.Result.Success_v
                                                                                                                      @lb16)
                                                                                                                    (FStar.Pervasives.Native.None Prims.int)))
                                                                                                                (forall
                                                                                                                  (
                                                                                                                    (@x19 Term))
                                                                                                                  (! (implies (HasType @x19 Prims.int) (Valid (ApplyTT @x18 @x19)))))))))))))
                                                                                                (implies
                                                                                                  (is-FStar.Tactics.Result.Failed
                                                                                                    @lb16)
                                                                                                  (Valid
                                                                                                    (ApplyTT
                                                                                                      @x14
                                                                                                      (FStar.Tactics.Result.Failed
                                                                                                        Prims.int
                                                                                                        (FStar.Tactics.Result.Failed_exn
                                                                                                          @lb16)
                                                                                                        (FStar.Tactics.Result.Failed_ps @lb16)))))))))))))
                                                                                (is-FStar.Tactics.Result.Failed @lb13)))
                                                                            (Valid (ApplyTT @x11 @x12)))
                                                                          :weight
                                                                          0
                                                                          :pattern
                                                                          ((ApplyTT @x11 @x12)))))
                                                                    (forall
                                                                      (
                                                                        (@x12 Term))
                                                                      (!
                                                                        (implies
                                                                          (HasType
                                                                            @x12
                                                                            (FStar.Tactics.Result.__result (FStar.Pervasives.Native.option Prims.int)))
                                                                          (let
                                                                            (
                                                                              (@lb13 @x12))
                                                                            (ite
                                                                              (is-FStar.Tactics.Result.Success
                                                                                @lb13)
                                                                              (forall
                                                                                (
                                                                                  (@x14 Term))
                                                                                (!
                                                                                  (implies
                                                                                    (and
                                                                                      (HasType
                                                                                        @x14
                                                                                        Tm_arrow_b8e144d0da1e757197d5cbec0bbcc261)
                                                                                      (forall
                                                                                        (
                                                                                          (@x15 Term))
                                                                                        (!
                                                                                          (implies
                                                                                            (Valid
                                                                                              (ApplyTT @x11 @x15))
                                                                                            (Valid (ApplyTT @x14 @x15)))
                                                                                          :weight
                                                                                          0
                                                                                          :pattern
                                                                                          ((ApplyTT @x14 @x15)))))
                                                                                    (forall
                                                                                      (
                                                                                        (@x15 Term))
                                                                                      (!
                                                                                        (implies
                                                                                          (and
                                                                                            (HasType
                                                                                              @x15
                                                                                              (Prims.pure_post Prims.int))
                                                                                            (forall
                                                                                              (
                                                                                                (@x16 Term))
                                                                                              (!
                                                                                                (implies
                                                                                                  (forall
                                                                                                    (
                                                                                                      (@x17 Term))
                                                                                                    (!
                                                                                                      (implies
                                                                                                        (and
                                                                                                          (HasType
                                                                                                            @x17
                                                                                                            Tm_arrow_b8e144d0da1e757197d5cbec0bbcc261)
                                                                                                          (forall
                                                                                                            (
                                                                                                              (@x18 Term))
                                                                                                            (!
                                                                                                              (implies
                                                                                                                (Valid
                                                                                                                  (ApplyTT @x14 @x18))
                                                                                                                (Valid (ApplyTT @x17 @x18)))
                                                                                                              :weight
                                                                                                              0
                                                                                                              :pattern
                                                                                                              ((ApplyTT @x17 @x18))))
                                                                                                          (=
                                                                                                            @x16
                                                                                                            (let
                                                                                                              (
                                                                                                                (@lb18 (FStar.Tactics.Result.Success_v @lb13)))
                                                                                                              (ite
                                                                                                                (is-FStar.Pervasives.Native.Some
                                                                                                                  @lb18)
                                                                                                                (FStar.Pervasives.Native.Some_v
                                                                                                                  @lb18)
                                                                                                                (ite (is-FStar.Pervasives.Native.None @lb18) (BoxInt 0) Tm_unit)))))
                                                                                                        (Valid
                                                                                                          (ApplyTT
                                                                                                            @x17
                                                                                                            (FStar.Tactics.Result.Success
                                                                                                              Prims.int
                                                                                                              @x16
                                                                                                              (FStar.Tactics.Result.Success_ps @lb13)))))))
                                                                                                  (Valid (ApplyTT @x15 @x16)))
                                                                                                :weight
                                                                                                0
                                                                                                :pattern
                                                                                                ((ApplyTT @x15 @x16)))))
                                                                                          (and
                                                                                            (implies
                                                                                              (and
                                                                                                (not
                                                                                                  (BoxBool_proj_0
                                                                                                    (FStar.Pervasives.Native.uu___is_Some
                                                                                                      Prims.int
                                                                                                      (FStar.Tactics.Result.Success_v @lb13))))
                                                                                                (not
                                                                                                  (BoxBool_proj_0
                                                                                                    (FStar.Pervasives.Native.uu___is_None
                                                                                                      Prims.int
                                                                                                      (FStar.Tactics.Result.Success_v @lb13)))))
                                                                                              label_6)
                                                                                            (forall
                                                                                              (
                                                                                                (@x16 Term))
                                                                                              (!
                                                                                                (implies
                                                                                                  (and
                                                                                                    (HasType
                                                                                                      @x16
                                                                                                      Prims.int)
                                                                                                    (=
                                                                                                      (FStar.Tactics.Result.Success_v
                                                                                                        @lb13)
                                                                                                      (FStar.Pervasives.Native.Some Prims.int @x16)))
                                                                                                  (forall
                                                                                                    (
                                                                                                      (@x17 Term))
                                                                                                    (! (implies (HasType @x17 Prims.int) (Valid (ApplyTT @x15 @x17))))))))
                                                                                            (implies
                                                                                              (and
                                                                                                (not
                                                                                                  (BoxBool_proj_0
                                                                                                    (FStar.Pervasives.Native.uu___is_Some
                                                                                                      Prims.int
                                                                                                      (FStar.Tactics.Result.Success_v @lb13))))
                                                                                                (=
                                                                                                  (FStar.Tactics.Result.Success_v
                                                                                                    @lb13)
                                                                                                  (FStar.Pervasives.Native.None Prims.int)))
                                                                                              (forall
                                                                                                (
                                                                                                  (@x16 Term))
                                                                                                (! (implies (HasType @x16 Prims.int) (Valid (ApplyTT @x15 @x16)))))))))))))
                                                                              (implies
                                                                                (is-FStar.Tactics.Result.Failed
                                                                                  @lb13)
                                                                                (Valid
                                                                                  (ApplyTT
                                                                                    @x11
                                                                                    (FStar.Tactics.Result.Failed
                                                                                      Prims.int
                                                                                      (FStar.Tactics.Result.Failed_exn
                                                                                        @lb13)
                                                                                      (FStar.Tactics.Result.Failed_ps @lb13)))))))))))))
                                                              (is-FStar.Tactics.Result.Failed @lb10)))
                                                          (Valid (ApplyTT @x8 @x9)))
                                                        :weight
                                                        0
                                                        :pattern
                                                        ((ApplyTT @x8 @x9)))))
                                                  (forall
                                                    ((@x9 Term))
                                                    (!
                                                      (implies
                                                        (HasType
                                                          @x9
                                                          (FStar.Tactics.Result.__result (FStar.Pervasives.Native.option Prims.int)))
                                                        (let
                                                          ((@lb10 @x9))
                                                          (ite
                                                            (is-FStar.Tactics.Result.Success
                                                              @lb10)
                                                            (forall
                                                              ((@x11 Term))
                                                              (!
                                                                (implies
                                                                  (and
                                                                    (HasType
                                                                      @x11
                                                                      Tm_arrow_b8e144d0da1e757197d5cbec0bbcc261)
                                                                    (forall
                                                                      (
                                                                        (@x12 Term))
                                                                      (!
                                                                        (implies
                                                                          (Valid
                                                                            (ApplyTT @x8 @x12))
                                                                          (Valid (ApplyTT @x11 @x12)))
                                                                        :weight
                                                                        0
                                                                        :pattern
                                                                        ((ApplyTT @x11 @x12)))))
                                                                  (forall
                                                                    (
                                                                      (@x12 Term))
                                                                    (!
                                                                      (implies
                                                                        (and
                                                                          (HasType
                                                                            @x12
                                                                            (Prims.pure_post Prims.int))
                                                                          (forall
                                                                            (
                                                                              (@x13 Term))
                                                                            (!
                                                                              (implies
                                                                                (forall
                                                                                  (
                                                                                    (@x14 Term))
                                                                                  (!
                                                                                    (implies
                                                                                      (and
                                                                                        (HasType
                                                                                          @x14
                                                                                          Tm_arrow_b8e144d0da1e757197d5cbec0bbcc261)
                                                                                        (forall
                                                                                          (
                                                                                            (@x15 Term))
                                                                                          (!
                                                                                            (implies
                                                                                              (Valid
                                                                                                (ApplyTT @x11 @x15))
                                                                                              (Valid (ApplyTT @x14 @x15)))
                                                                                            :weight
                                                                                            0
                                                                                            :pattern
                                                                                            ((ApplyTT @x14 @x15))))
                                                                                        (=
                                                                                          @x13
                                                                                          (let
                                                                                            (
                                                                                              (@lb15 (FStar.Tactics.Result.Success_v @lb10)))
                                                                                            (ite
                                                                                              (is-FStar.Pervasives.Native.Some
                                                                                                @lb15)
                                                                                              (FStar.Pervasives.Native.Some_v
                                                                                                @lb15)
                                                                                              (ite (is-FStar.Pervasives.Native.None @lb15) (BoxInt 0) Tm_unit)))))
                                                                                      (Valid
                                                                                        (ApplyTT
                                                                                          @x14
                                                                                          (FStar.Tactics.Result.Success
                                                                                            Prims.int
                                                                                            @x13
                                                                                            (FStar.Tactics.Result.Success_ps @lb10)))))))
                                                                                (Valid (ApplyTT @x12 @x13)))
                                                                              :weight
                                                                              0
                                                                              :pattern
                                                                              ((ApplyTT @x12 @x13)))))
                                                                        (and
                                                                          (implies
                                                                            (and
                                                                              (not
                                                                                (BoxBool_proj_0
                                                                                  (FStar.Pervasives.Native.uu___is_Some
                                                                                    Prims.int
                                                                                    (FStar.Tactics.Result.Success_v @lb10))))
                                                                              (not
                                                                                (BoxBool_proj_0
                                                                                  (FStar.Pervasives.Native.uu___is_None
                                                                                    Prims.int
                                                                                    (FStar.Tactics.Result.Success_v @lb10)))))
                                                                            label_7)
                                                                          (forall
                                                                            (
                                                                              (@x13 Term))
                                                                            (!
                                                                              (implies
                                                                                (and
                                                                                  (HasType
                                                                                    @x13
                                                                                    Prims.int)
                                                                                  (=
                                                                                    (FStar.Tactics.Result.Success_v
                                                                                      @lb10)
                                                                                    (FStar.Pervasives.Native.Some Prims.int @x13)))
                                                                                (forall
                                                                                  (
                                                                                    (@x14 Term))
                                                                                  (! (implies (HasType @x14 Prims.int) (Valid (ApplyTT @x12 @x14))))))))
                                                                          (implies
                                                                            (and
                                                                              (not
                                                                                (BoxBool_proj_0
                                                                                  (FStar.Pervasives.Native.uu___is_Some
                                                                                    Prims.int
                                                                                    (FStar.Tactics.Result.Success_v @lb10))))
                                                                              (=
                                                                                (FStar.Tactics.Result.Success_v
                                                                                  @lb10)
                                                                                (FStar.Pervasives.Native.None Prims.int)))
                                                                            (forall
                                                                              (
                                                                                (@x13 Term))
                                                                              (! (implies (HasType @x13 Prims.int) (Valid (ApplyTT @x12 @x13)))))))))))))
                                                            (implies
                                                              (is-FStar.Tactics.Result.Failed
                                                                @lb10)
                                                              (Valid
                                                                (ApplyTT
                                                                  @x8
                                                                  (FStar.Tactics.Result.Failed
                                                                    Prims.int
                                                                    (FStar.Tactics.Result.Failed_exn
                                                                      @lb10)
                                                                    (FStar.Tactics.Result.Failed_ps @lb10)))))))))))))
                                            (is-FStar.Tactics.Result.Failed @lb7)))
                                        (Valid (ApplyTT @x5 @x6)))
                                      :weight
                                      0
                                      :pattern
                                      ((ApplyTT @x5 @x6)))))
                                (forall
                                  ((@x6 Term))
                                  (!
                                    (implies
                                      (HasType
                                        @x6
                                        (FStar.Tactics.Result.__result (FStar.Pervasives.Native.option Prims.int)))
                                      (let
                                        ((@lb7 @x6))
                                        (ite
                                          (is-FStar.Tactics.Result.Success
                                            @lb7)
                                          (forall
                                            ((@x8 Term))
                                            (!
                                              (implies
                                                (and
                                                  (HasType
                                                    @x8
                                                    Tm_arrow_b8e144d0da1e757197d5cbec0bbcc261)
                                                  (forall
                                                    ((@x9 Term))
                                                    (!
                                                      (implies
                                                        (Valid
                                                          (ApplyTT @x5 @x9))
                                                        (Valid (ApplyTT @x8 @x9)))
                                                      :weight
                                                      0
                                                      :pattern
                                                      ((ApplyTT @x8 @x9)))))
                                                (forall
                                                  ((@x9 Term))
                                                  (!
                                                    (implies
                                                      (and
                                                        (HasType
                                                          @x9
                                                          (Prims.pure_post Prims.int))
                                                        (forall
                                                          ((@x10 Term))
                                                          (!
                                                            (implies
                                                              (forall
                                                                ((@x11 Term))
                                                                (!
                                                                  (implies
                                                                    (and
                                                                      (HasType
                                                                        @x11
                                                                        Tm_arrow_b8e144d0da1e757197d5cbec0bbcc261)
                                                                      (forall
                                                                        (
                                                                          (@x12 Term))
                                                                        (!
                                                                          (implies
                                                                            (Valid
                                                                              (ApplyTT @x8 @x12))
                                                                            (Valid (ApplyTT @x11 @x12)))
                                                                          :weight
                                                                          0
                                                                          :pattern
                                                                          ((ApplyTT @x11 @x12))))
                                                                      (=
                                                                        @x10
                                                                        (let
                                                                          (
                                                                            (@lb12 (FStar.Tactics.Result.Success_v @lb7)))
                                                                          (ite
                                                                            (is-FStar.Pervasives.Native.Some
                                                                              @lb12)
                                                                            (FStar.Pervasives.Native.Some_v
                                                                              @lb12)
                                                                            (ite (is-FStar.Pervasives.Native.None @lb12) (BoxInt 0) Tm_unit)))))
                                                                    (Valid
                                                                      (ApplyTT
                                                                        @x11
                                                                        (FStar.Tactics.Result.Success
                                                                          Prims.int
                                                                          @x10
                                                                          (FStar.Tactics.Result.Success_ps @lb7)))))))
                                                              (Valid (ApplyTT @x9 @x10)))
                                                            :weight
                                                            0
                                                            :pattern
                                                            ((ApplyTT @x9 @x10)))))
                                                      (and
                                                        (implies
                                                          (and
                                                            (not
                                                              (BoxBool_proj_0
                                                                (FStar.Pervasives.Native.uu___is_Some
                                                                  Prims.int
                                                                  (FStar.Tactics.Result.Success_v @lb7))))
                                                            (not
                                                              (BoxBool_proj_0
                                                                (FStar.Pervasives.Native.uu___is_None
                                                                  Prims.int
                                                                  (FStar.Tactics.Result.Success_v @lb7)))))
                                                          label_8)
                                                        (forall
                                                          ((@x10 Term))
                                                          (!
                                                            (implies
                                                              (and
                                                                (HasType
                                                                  @x10
                                                                  Prims.int)
                                                                (=
                                                                  (FStar.Tactics.Result.Success_v
                                                                    @lb7)
                                                                  (FStar.Pervasives.Native.Some Prims.int @x10)))
                                                              (forall
                                                                ((@x11 Term))
                                                                (! (implies (HasType @x11 Prims.int) (Valid (ApplyTT @x9 @x11))))))))
                                                        (implies
                                                          (and
                                                            (not
                                                              (BoxBool_proj_0
                                                                (FStar.Pervasives.Native.uu___is_Some
                                                                  Prims.int
                                                                  (FStar.Tactics.Result.Success_v @lb7))))
                                                            (=
                                                              (FStar.Tactics.Result.Success_v
                                                                @lb7)
                                                              (FStar.Pervasives.Native.None Prims.int)))
                                                          (forall
                                                            ((@x10 Term))
                                                            (! (implies (HasType @x10 Prims.int) (Valid (ApplyTT @x9 @x10)))))))))))))
                                          (implies
                                            (is-FStar.Tactics.Result.Failed
                                              @lb7)
                                            (Valid
                                              (ApplyTT
                                                @x5
                                                (FStar.Tactics.Result.Failed
                                                  Prims.int
                                                  (FStar.Tactics.Result.Failed_exn
                                                    @lb7)
                                                  (FStar.Tactics.Result.Failed_ps @lb7)))))))))))))
                          (is-FStar.Tactics.Result.Failed @lb4)))
                      (Valid (ApplyTT @x2 @x3)))
                    :weight
                    0
                    :pattern
                    ((ApplyTT @x2 @x3)))))
              (forall
                ((@x3 Term))
                (!
                  (implies
                    (HasType
                      @x3
                      (FStar.Tactics.Result.__result (FStar.Pervasives.Native.option Prims.int)))
                    (let
                      ((@lb4 @x3))
                      (ite
                        (is-FStar.Tactics.Result.Success @lb4)
                        (forall
                          ((@x5 Term))
                          (!
                            (implies
                              (and
                                (HasType
                                  @x5
                                  Tm_arrow_b8e144d0da1e757197d5cbec0bbcc261)
                                (forall
                                  ((@x6 Term))
                                  (implies (Valid (ApplyTT @x2 @x6)) (Valid (ApplyTT @x5 @x6)))))
                              (forall
                                ((@x6 Term))
                                (!
                                  (implies
                                    (and
                                      (HasType
                                        @x6
                                        (Prims.pure_post Prims.int))
                                      (forall
                                        ((@x7 Term))
                                        (!
                                          (implies
                                            (forall
                                              ((@x8 Term))
                                              (!
                                                (implies
                                                  (and
                                                    (HasType
                                                      @x8
                                                      Tm_arrow_b8e144d0da1e757197d5cbec0bbcc261)
                                                    (forall
                                                      ((@x9 Term))
                                                      (!
                                                        (implies
                                                          (Valid
                                                            (ApplyTT @x5 @x9))
                                                          (Valid (ApplyTT @x8 @x9)))
                                                        :weight
                                                        0
                                                        :pattern
                                                        ((ApplyTT @x8 @x9))))
                                                    (=
                                                      @x7
                                                      (let
                                                        (
                                                          (@lb9 (FStar.Tactics.Result.Success_v @lb4)))
                                                        (ite
                                                          (is-FStar.Pervasives.Native.Some
                                                            @lb9)
                                                          (FStar.Pervasives.Native.Some_v
                                                            @lb9)
                                                          (ite (is-FStar.Pervasives.Native.None @lb9) (BoxInt 0) Tm_unit)))))
                                                  (Valid
                                                    (ApplyTT
                                                      @x8
                                                      (FStar.Tactics.Result.Success
                                                        Prims.int
                                                        @x7
                                                        (FStar.Tactics.Result.Success_ps @lb4)))))))
                                            (Valid (ApplyTT @x6 @x7)))
                                          :weight
                                          0
                                          :pattern
                                          ((ApplyTT @x6 @x7)))))
                                    (and
                                      (implies
                                        (and
                                          (not
                                            (BoxBool_proj_0
                                              (FStar.Pervasives.Native.uu___is_Some
                                                Prims.int
                                                (FStar.Tactics.Result.Success_v @lb4))))
                                          (not
                                            (BoxBool_proj_0
                                              (FStar.Pervasives.Native.uu___is_None
                                                Prims.int
                                                (FStar.Tactics.Result.Success_v @lb4)))))
                                        label_9)
                                      (forall
                                        ((@x7 Term))
                                        (!
                                          (implies
                                            (and
                                              (HasType @x7 Prims.int)
                                              (=
                                                (FStar.Tactics.Result.Success_v
                                                  @lb4)
                                                (FStar.Pervasives.Native.Some Prims.int @x7)))
                                            (forall
                                              ((@x8 Term))
                                              (! (implies (HasType @x8 Prims.int) (Valid (ApplyTT @x6 @x8))))))))
                                      (implies
                                        (and
                                          (not
                                            (BoxBool_proj_0
                                              (FStar.Pervasives.Native.uu___is_Some
                                                Prims.int
                                                (FStar.Tactics.Result.Success_v @lb4))))
                                          (=
                                            (FStar.Tactics.Result.Success_v
                                              @lb4)
                                            (FStar.Pervasives.Native.None Prims.int)))
                                        (forall
                                          ((@x7 Term))
                                          (! (implies (HasType @x7 Prims.int) (Valid (ApplyTT @x6 @x7)))))))))))))
                        true))))))))))))
(check-sat)
