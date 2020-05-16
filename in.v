
Add LoadPath ".".
Load BenB.

Load BenB2.

(* ====================================================================== *)

(*
Praktika super TL artifact
======
Authors:
Jozef Coldenhoff      s1017656
Charlotte Frenzen     s4739760
Nils Golembiewski     s1019649
Noah van der Vleuten  s1018323
*)

(* ====================================================================== *)

(*
[
    This file has to be a valid script, meaning that it
    can be executed by Coq.
    Therefore, explanations in natural language have to be between
    comment markers.

    In this project template, text within square brackets (within
    comment markers) is intended to clarify what needs to be
    written where.

    In the final version, we expect that all these blocks have been
    replaced by (your) proper content.
]

*)

(*
Abstract:
=========
[
    Explain whether you managed to prove the correctness theorem.
    And how did that go: did you have to change a lot compared to
    the original model as it was before you started with the proof,
    or could you use your formalization without many modifications?
]

*)

(*
Focus:


Modeling Goal:
==============
[Verification model]


Fragment of reality:
====================
[
Our model will focus on the user of the camera, the camera itself,
and the visual representation of the world within the scope of the lens
and the film inside of the camera.
]


Perspective:
============
[
Save selected visual state of world within the scope of the lens on film.
]

*)


(*
Abstractions or simplifications:
================================
[
    Depending on the chosen focus, you may simplify certain aspects of
    your artifact.
    If you are modeling some kind of home automation system, it is not
    unreasonable to assume that the net power is constant, although this
    is not exactly the case in reality. However, if you are modeling an
    artifact that protects against high peaks of power, these fluctuations
    should be part of the model.

    Write down explicitly which assumptions you have made to simplify
    the artifact.
]

We have chosen not to model the viewfinder of the camera.
We did this because we thought it would add unnecessary complexity that doesn't really help prove what we're trying to prove.
*)

(* ====================================================================== *)

(* Domain model *)

(* Domains (including their meaning) *)
Definition T := R.
(* Time as minutes in real numbers. *)

Variable SS : Set.
(* Set of all shutter speed settings. *)

Variable AS : Set.
(* All aperture settings. *)

Variable FS : Set.
(* All focus settings. *)

(* Constants (including their meaning) *)

(* Functions (including their meaning) *)
Variable ShutterTime : SS -> T.
(* Gives the associated amount of time of the shutter setting. *)

(* Predicates (including their meaning and measurements) *)

Variable hasPowerAt (* t *) : T -> Prop.
(* Components have power at time t. *)
(* Check if the internal spring in the camera is loaded. *)

Variable focusSelectorTurnedToAt (* fs t *) : FS -> T -> Prop.
(* The focus selector was turned to setting fs at time t. *)
(* Ask the user of the camera if he/she turned the focus selector. *)

Variable apertureSelectorTurnedToAt (* as t *) : AS -> T -> Prop.
(* The aperture selector was turned to setting as at time t. *)
(* Ask the user of the camera if he/she turned the aperture selector. *)

Variable shutterSelectorTurnedToAt (* ss t *) : SS -> T -> Prop.
(* The shutter speed selector was turned to setting ss at time t. *)
(* Ask the user of the camera if he/she turned the shutter speed selector. *)

Variable leverPulledAt (* t *) : T -> Prop.
(* The lever was pulled at time t. *)
(* Ask the user if and when the lever was pulled. *)

Variable visualWorldStateInScopeAt (* t *) : T -> Prop .
(* There is light entering the lens at time t. *)
(* Look through the viewfinder. *)

Variable shutterButtonPressedAt (* t *) : T -> Prop.
(* The shutter button was pressed at time t. *)
(* Ask the user of the camera if and when the shutter button was pressed. *)

Variable filmRollLoadedAt (* t *) : T -> Prop.
(* At time t the camera contains a roll of film. *)
(* Look if there is a roll of film in the camera. *)

Variable shutterSettingAt (* s t *) : SS -> T -> Prop.
(* Shutter setting s is present at time t. *)
(* Check the shutter selector wheel at time t. *)

Variable apertureSettingAt (* s t *) : AS -> T -> Prop.
(* Aperture setting s is present at time t. *)
(* Check the aperture selector ring at time t. *)

Variable focusSettingAt (* s t *) : FS -> T -> Prop.
(* Focus setting s is present at time t. *)
(* Check the focus selector ring at time t. *)

Variable apertureContractedAt (* t *) : T -> Prop.
(* The aperture is contracted at time t. *)
(* Look at the aperture at time t. *)

Variable shutterOpenAt (* t *) : T -> Prop.
(* The shutter is open at time t. *)
(* Look whether the shutter is open at time t. *)

Variable mirrorUpAt (* t *) : T -> Prop.
(* The mirror is up at time t. *)
(* Look if the viewfinder is dark. *)

Variable focussedLensLightAt (* t *) :  T -> Prop.
(* Focussed lens light is available at time t. *)
(* Look through the viewfinder to see if the picture taken is in focus. *)

Variable selectedVisualWorldStateSavedOnFilm (* fs as1 ss t *) : FS -> AS -> SS -> T -> Prop.
(* The selected picture negative was saved on film at time t. *)
(* Develop the film and see if it is the picture that was meant to be taken. *)

(* ====================================================================== *)

(* Auxiliary predicates (including their meaning) *)

(*
[
    At this place within this template you may define as many
    auxiliary predicates as you want, but do not forget to include
    their meaning.
]
*)

(* ====================================================================== *)

(* Components *)
Definition Lever :=
forall t : T,
        leverPulledAt t
    ->
        (
            forall d : T,
                        shutterButtonPressedAt (t+d)
                    /\
                        d > 0
                    /\
                            (
                            forall d2 : T,
                                    d2 in [t, t+d)
                                ->
                                    ~shutterButtonPressedAt d2
                            )
                ->
                    (
                        forall i : T,
                                i in [t, t+d]
                            ->
                                hasPowerAt i
                    )
        )
.

(*
Meaning Lever:
If at any point in time the lever is pulled, then,
the first time the shutter button is pressed after that point,
the components have power from the time the lever is pulled
until the time the shutter button is pressed.
*)

Definition ShutterSpeedSelectorWheel :=
forall (t : T) (ss : SS),
    shutterSelectorTurnedToAt ss t
->

            (
                forall d: T,
                            d >= 0
                            (* possibly replace by t2 where t2 = t+d *)
                        /\
                            (
                                forall ss2 : SS,
                                        ss <> ss2
                                    ->
                                        (
                                            forall x: T,
                                                    x in [t, t+d]
                                                ->
                                                    ~ shutterSelectorTurnedToAt ss2 x
                                        )
                            )
                    ->
                        shutterSettingAt ss (t+d)
            )
.

(*
Meaning ShutterSpeedSelectorWheel:

If at any point in time the shutter time selector is turned to a specific (first) setting,
then, if there is any point in the future at which the shutter time selector is 
turned to another setting, the shutter setting is set to the first setting until that point
at which the shutter time selector is turned to the other setting. And, if there is no
point in the future at which the shutter time selector is turned to another setting,
the setting will always be the first setting in the future.
*)

Definition ApertureSelectorRing :=
forall (t : T) (as1 : AS),
    apertureSelectorTurnedToAt as1 t
->
        (
            forall d: T,
                        d >= 0
                    /\
                        (
                            forall as2 : AS,
                                    as1 <> as2
                                ->
                                    (
                                        forall x: T,
                                                x in [t, t+d]
                                            ->
                                                ~ apertureSelectorTurnedToAt as2 x
                                    )
                                                    
                        )
                ->
                    apertureSettingAt as1 (t+d)
        )
.

(*
Meaning ApertureSelectorRing:

If at any point in time the aperture selector is turned to a specific (first) setting,
then, if there is any point in the future at which the aperture selector is 
turned to another setting, the aperture setting is set to the first setting until that point
at which the aperture selector is turned to the other setting. And, if there is no
point in the future at which the aperture selector is turned to another setting,
the setting will always be the first setting in the future.
*)

Definition FocusSelectorRing :=
forall (t : T) (fs : FS),
    focusSelectorTurnedToAt fs t
->
        (
                forall d: T,
                            d >= 0
                        /\
                                (
                                    forall fs2 : FS,
                                            fs <> fs2
                                        ->
                                            (
                                                forall x: T,
                                                        x in [t, t+d]
                                                    ->
                                                        ~ focusSelectorTurnedToAt fs2 x
                                            )
                                        
                                )
                    ->
                        focusSettingAt fs (t+d)
        )
.

(*
Meaning FocusSelectorRing:

If at any point in time the focus selector is turned to a specific (first) setting,
then, if there is any point in the future at which the focus selector is 
turned to another setting, the focus setting is set to the first setting until that point
at which the focus selector is turned to the other setting. And, if there is no
point in the future at which the focus selector is turned to another setting,
the setting will always be the first setting in the future.
*)

Definition Lens:=
forall (t : T) (fs : FS),
        focusSettingAt fs t
    /\
        visualWorldStateInScopeAt t
->
    focussedLensLightAt t
.
(*
Meaning Lens:

If at any point in time the focus setting is set to a specific setting,
and the visual state of the world is in scope at that time,
then there is focussed lens light at that time.
*)

Definition Shutter :=
forall (t : T) (ss : SS),
        shutterSettingAt ss t
    /\
        hasPowerAt t
    /\
        shutterButtonPressedAt t
->
    (
        forall d :T,
                d in [t, t + ShutterTime ss]
            ->
                shutterOpenAt d
    )
.

(*
Meaning Shutter:

If at any point in time, the shutter setting is a specific setting, and the components have power
and the shutter button is pressed, then the shutter is open from that point time, until that
point in time plus the interval specified by the shutter setting.
*)

Definition Aperture:=
forall (t : T) (ss : SS) (as1 : AS),
        shutterSettingAt ss t
    /\
        hasPowerAt t
    /\
        shutterButtonPressedAt t
    /\
        apertureSettingAt as1 t
->
    (
            forall d :T,
                d in [t, t + ShutterTime ss]
            ->
                apertureContractedAt d
    )
.

(*
Meaning Aperture:

If at any point in time, the shutter setting is a specific setting, the components have power, 
the shutter button is pressed and the aperture setting is a specific setting,   
then the aperture is contracted from that point time, until that
point in time plus the interval specified by the shutter setting.
*)

Definition Mirror :=
forall (t : T) (ss : SS),
        shutterSettingAt ss t
    /\
        hasPowerAt t
    /\
        shutterButtonPressedAt t
->
    (
        forall d :T,
                d in [t, t + ShutterTime ss]
            ->
                mirrorUpAt d
    )
.

(*
Meaning Mirror:

If at any point in time, the shutter setting is a specific setting, the components have power, 
the shutter button is pressed,    
then the mirror is up from that point time, until that
point in time plus the interval specified by the shutter setting.
*)

Definition Film :=
forall (t : T) (ss : SS) (as1 : AS) (fs : FS),
        filmRollLoadedAt t
    /\
        shutterSettingAt ss t
    /\
        focusSettingAt fs t
    /\
        apertureSettingAt as1 t
    /\
        (
            forall i: T,
                    i in [t, t + (ShutterTime ss))
                ->
                        shutterOpenAt i
                    /\
                        mirrorUpAt i
                    /\
                        apertureContractedAt i
                    /\
                        focussedLensLightAt i
        )
->
    selectedVisualWorldStateSavedOnFilm fs as1 ss (t + (ShutterTime ss))
.

(*
Meaning film:

If at some point in time, the shutter setting is set to a specific setting,
and the forcus setting is set to a specific setting, and the aperture setting is
set to a specific setting and, the mirror is up, and the aperture is contracted,
and there is focused lens light from the point in time until as long as the shutter
time setting specifies, then the selected visual world state at the point in time plus
the shutter time is saved on film with the shutter setting, focus setting and shutter setting.
*)

(*
[
    For each component you have to specify the following information:

    OUTSIDE comment markers:
    - The 'Definition' to be read by Coq, in a readable layout that
    matches the mathematical structure of the formula.

    WITHIN comment markers:
    - The specification of the component in natural language. Obviously,
    this specification should be consistent with the formula used
    by Coq.
    - If appropriate, a short explanation in natural language about
    the choices that have been made.
]
*)

(* ====================================================================== *)

(* Specification of the overall system *)
Definition Camera :=
forall (t1 : T) (t2 : T) (t3 : T) (ss : SS) (as1 : AS) (fs : FS),
        t2 > t1
    /\
        t3 > t2
    /\
    filmRollLoadedAt t3
    /\
    ShutterTime ss > 0
    /\
        (
            forall t : T,
                    t in [t1, t3 + ShutterTime ss]
                ->
                    (
                            (
                                forall as2 : AS,
                                        as1 <> as2
                                    ->
                                        ~apertureSelectorTurnedToAt as2 t
                            )
                        /\
                            (
                                forall ss2 : SS,
                                        ss <> ss2
                                    -> 
                                        ~shutterSelectorTurnedToAt ss2 t
                            )
                        /\
                            (
                                forall fs2 : FS,
                                        fs <> fs2
                                    ->
                                        ~ focusSelectorTurnedToAt fs2 t
                            )
                )
        )
    /\
        (
            exists y1 : T,
                    y1 in [t1, t2 )
                /\
                    leverPulledAt y1
        )
    /\
        (
            forall t : T,
                    t in [t1, t3)
                ->
                    ~ shutterButtonPressedAt t
        )
    /\
        (
            exists y2 : T,
                    y2 in [t2, t3 )
                /\
                    focusSelectorTurnedToAt fs y2
                /\
                    apertureSelectorTurnedToAt as1 y2
                /\
                    shutterSelectorTurnedToAt ss  y2
        )
    /\
        (
            forall y3: T,
                    y3 in [t3 , t3 + (ShutterTime ss))
                ->
                    visualWorldStateInScopeAt y3
        )
    /\
        shutterButtonPressedAt t3
->
    selectedVisualWorldStateSavedOnFilm fs as1 ss (t3 + (ShutterTime ss))
.

(*
Meaning Camera:

For any three subsequent points in time and any shutter, aperture and focus setting, 
if at the first point in time the lever is pulled, and at the second point in time the aperture, 
shutter and, focus settings are set and are not changed until the shutter button is pressed, 
and if we press the shutter button no earlier or later than the third point in time, 
then the photo is saved on film after a short time after the third point in time that is associated with the chosen shutter speed setting.
*)

(*
[
    Here you have to specify:

    OUTSIDE comment markers:
    - The 'Definition' to be read by Coq, in a readable layout that
    matches the mathematical structure of the formula.

    WITHIN comment markers:
    - The specification of the overall system in natural language.
    Obviously, this specification should be consistent with the
    formula used by Coq.
    - If appropriate, a short explanation in natural language about
    the choices that have been made.
]
*)

(* ====================================================================== *)

(* Extras *)

(*
[
    It is very likely that you do not need any extras!

    However, if it turns out during your proof that you have to prove
    several times (almost) the same, then you may define a 'Lemma' at
    this place, followed by its proof. And in the proof of the correctness
    theorem, you may apply this lemma several times.
    Note that it is always allowed to add lemmas to this script!

    Sometimes it happens that Coq has troubles with 'trivial' properties
    of numbers, that cannot be solve easily using 'lin_solve'.
    In such situations, you may contact your supervisor and discuss
    whether this may be solved by adding an 'Axiom', which can also be
    applied later on within the proof of the correctness theorem.
]
*)

(* Correctness theorem *)

(* ====================================================================== *)

(*
[
    Write down your correctness theorem in the usual notation:
    Theorem CorTheorem:
    Component1 /\ Component2 /\ ... /\ ComponentN -> SpecOfTheOverallSystem.

    Note that as long as you don't know what natural deduction is
    and you cannot start with the proof yet, you should keep this
    theorem within comment markers, otherwise you will get a red cross
    for stating a theorem without a proof.

    For the final version you obviously have to remove these comment
    markers and provide a real proof!

    Note that even if your proof is correct, you won't be able to
    get a green check mark, but only an orange flag, for technical
    reasons. But that is no problem.
]
*)

Theorem CorTheorem:
            Lever
        /\
            Lens
        /\
            Mirror
        /\
            Aperture
        /\
            Shutter
        /\
            Film
        /\
            ShutterSpeedSelectorWheel
        /\
            ApertureSelectorRing
        /\
            FocusSelectorRing
->
    Camera
.
Proof.
unfold Lever.
unfold Lens.
unfold Mirror.
unfold Aperture.
unfold Shutter.
unfold Film.
unfold ShutterSpeedSelectorWheel.
unfold ApertureSelectorRing.
unfold FocusSelectorRing.
unfold Camera.
imp_i a1.
destruct a1.
destruct H0.
destruct H1.
destruct H2.
destruct H3.
destruct H4.
destruct H5.
destruct H6.
all_i t1_strict.
all_i t2_strict.
all_i t3_strict.
all_i ss_strict.
all_i as1_strict.
all_i fs_strict.
imp_i a2.
destruct a2.
destruct H9.
destruct H10.
destruct H11.
destruct H12.
destruct H13.
destruct H14.
destruct H15.
destruct H16.
exi_e (exists y1 : T, y1 in [t1_strict, t2_strict) /\ leverPulledAt y1)
    y1_strict a3
.
hyp H13.
destruct a3.
exi_e (exists y2 : T,
        y2 in [t2_strict, t3_strict)
                /\
                focusSelectorTurnedToAt fs_strict y2
                /\
                apertureSelectorTurnedToAt as1_strict y2
                /\
                shutterSelectorTurnedToAt ss_strict y2
    )
    y2_strict a4
.
hyp H15.
destruct a4.
destruct H21.
destruct H22.
exi_e (exists d:T, d = (t3_strict - y2_strict) ) d_strict a5.
exi_i (t3_strict - y2_strict).
lin_solve.
imp_e (
    filmRollLoadedAt t3_strict
    /\
    shutterSettingAt ss_strict t3_strict
    /\
    focusSettingAt fs_strict t3_strict
    /\
    apertureSettingAt as1_strict t3_strict
    /\
    (forall i : T,
        i in [t3_strict, t3_strict + ShutterTime ss_strict)
            ->
            shutterOpenAt i
            /\
            mirrorUpAt i
            /\
            apertureContractedAt i
            /\
            focussedLensLightAt i
    )
).
all_e (forall (fs : FS),
        filmRollLoadedAt t3_strict
        /\
        shutterSettingAt ss_strict t3_strict
        /\
        focusSettingAt fs t3_strict
        /\
        apertureSettingAt as1_strict t3_strict
        /\
        (forall i : T,
            i in [t3_strict, t3_strict + ShutterTime ss_strict)
                    ->
                    shutterOpenAt i
                    /\
                    mirrorUpAt i
                    /\
                    apertureContractedAt i
                    /\
                    focussedLensLightAt i)
        ->
        selectedVisualWorldStateSavedOnFilm fs as1_strict ss_strict (t3_strict + ShutterTime ss_strict)
    )
    fs_strict.  
all_e (forall (as1 : AS)(fs : FS),
        filmRollLoadedAt t3_strict
        /\
        shutterSettingAt ss_strict t3_strict
        /\
        focusSettingAt fs t3_strict
        /\
        apertureSettingAt as1 t3_strict
        /\
        (forall i : T,
            i in [t3_strict, t3_strict + ShutterTime ss_strict)
                    ->
                    shutterOpenAt i
                    /\
                    mirrorUpAt i
                    /\
                    apertureContractedAt i
                    /\
                    focussedLensLightAt i)
        ->
        selectedVisualWorldStateSavedOnFilm fs as1 ss_strict (t3_strict + ShutterTime ss_strict)
    )
    as1_strict
.
all_e (forall (ss : SS) (as1 : AS) (fs : FS),
        filmRollLoadedAt t3_strict
        /\
        shutterSettingAt ss t3_strict
        /\
        focusSettingAt fs t3_strict
        /\
        apertureSettingAt as1 t3_strict
        /\
        (forall i : T,
            i in [t3_strict, t3_strict + ShutterTime ss)
                    ->
                    shutterOpenAt i
                    /\
                    mirrorUpAt i
                    /\
                    apertureContractedAt i
                    /\
                    focussedLensLightAt i)
        ->
        selectedVisualWorldStateSavedOnFilm fs as1 ss (t3_strict + ShutterTime ss)
    )
    ss_strict
.
all_e (forall (t:T) (ss : SS) (as1 : AS)(fs : FS),
        filmRollLoadedAt t
        /\
        shutterSettingAt ss t
        /\
        focusSettingAt fs t
        /\
        apertureSettingAt as1 t
        /\
        (forall i : T,
            i in [t, t + ShutterTime ss)
                    ->
                    shutterOpenAt i
                    /\
                    mirrorUpAt i
                    /\
                    apertureContractedAt i
                    /\
                    focussedLensLightAt i)
        ->
        selectedVisualWorldStateSavedOnFilm fs as1 ss (t + ShutterTime ss)
    )
    t3_strict
.
hyp H4.
con_i.
hyp H10.

imp_e (apertureSettingAt as1_strict t3_strict).
imp_i a_aperture_setting.

imp_e (focusSettingAt fs_strict t3_strict).
imp_i a_focus_setting.

imp_e (shutterSettingAt ss_strict t3_strict).
imp_i a_shutter_setting.

imp_e (hasPowerAt t3_strict).
imp_i a_has_power.
(*
imp_e (forall t:T, t in [t1_strict, t3_strict] -> t in [t1_strict, t3_strict  + ShutterTime ss_strict]).
imp_i a_interval1.
*)
con_i.
hyp a_shutter_setting.
con_i.
hyp a_focus_setting.
con_i.
hyp a_aperture_setting.
all_i i_strict.
imp_i ab1.
con_i.

(*=============shutteropenedat=========*)

imp_e (i_strict in [t3_strict, t3_strict + ShutterTime ss_strict]).
all_e (forall d : T, d in [t3_strict, t3_strict + ShutterTime ss_strict] -> shutterOpenAt d) i_strict.
imp_e (shutterSettingAt ss_strict t3_strict /\ hasPowerAt t3_strict /\ shutterButtonPressedAt t3_strict).
all_e (forall (ss : SS),
        shutterSettingAt ss t3_strict
        /\
        hasPowerAt t3_strict
        /\
        shutterButtonPressedAt t3_strict
        ->
        (forall d : T, d in [t3_strict, t3_strict + ShutterTime ss] -> shutterOpenAt d)
    )
    ss_strict
.
all_e (forall (t : T) (ss : SS),
        shutterSettingAt ss t
        /\
        hasPowerAt t
        /\
        shutterButtonPressedAt t
        ->
        (forall d : T, d in [t, t + ShutterTime ss] -> shutterOpenAt d))
    t3_strict
.
hyp H3.
con_i.
hyp a_shutter_setting.
con_i.
hyp a_has_power.
hyp H17.
interval.
imp_e (t3_strict <= i_strict /\ i_strict < t3_strict + ShutterTime ss_strict).
imp_i ab2.
con_i.
con_e1 (i_strict < t3_strict + ShutterTime ss_strict).
hyp ab2.
imp_e (i_strict < t3_strict + ShutterTime ss_strict).
imp_i abc1.
lin_solve.
con_e2 (t3_strict <= i_strict).
hyp ab2.
hyp ab1.


(*===============mirrorupat=================*)
con_i.
imp_e (i_strict in [t3_strict, t3_strict + ShutterTime ss_strict]).
all_e (forall d : T, d in [t3_strict, t3_strict + ShutterTime ss_strict] -> mirrorUpAt d) i_strict.
imp_e (shutterSettingAt ss_strict t3_strict /\ hasPowerAt t3_strict /\ shutterButtonPressedAt t3_strict).
all_e (forall (ss : SS),
        shutterSettingAt ss t3_strict
        /\
        hasPowerAt t3_strict
        /\
        shutterButtonPressedAt t3_strict
        ->
        (forall d : T, d in [t3_strict, t3_strict + ShutterTime ss] -> mirrorUpAt d)
    )
    ss_strict
.
all_e (forall (t : T) (ss : SS),
        shutterSettingAt ss t
        /\
        hasPowerAt t
        /\
        shutterButtonPressedAt t
        ->
        (forall d : T, d in [t, t + ShutterTime ss] -> mirrorUpAt d))
    t3_strict
.
hyp H1.
con_i.
hyp a_shutter_setting.
con_i.
hyp a_has_power.
hyp H17.
interval.
imp_e (t3_strict <= i_strict /\ i_strict < t3_strict + ShutterTime ss_strict).
imp_i ab2.
con_i.
con_e1 (i_strict < t3_strict + ShutterTime ss_strict).
hyp ab2.
imp_e (i_strict < t3_strict + ShutterTime ss_strict).
imp_i abc1.
lin_solve.
con_e2 (t3_strict <= i_strict).
hyp ab2.
hyp ab1.

(*=======aperturecontractedat========*)
con_i.
imp_e (i_strict in [t3_strict, t3_strict + ShutterTime ss_strict]).
all_e (forall d : T, d in [t3_strict, t3_strict + ShutterTime ss_strict] -> apertureContractedAt d) i_strict.
imp_e (
    shutterSettingAt ss_strict t3_strict
    /\
    hasPowerAt t3_strict
    /\
    shutterButtonPressedAt t3_strict
    /\
    apertureSettingAt as1_strict t3_strict
)
.
all_e (forall (as1 : AS),
        shutterSettingAt ss_strict t3_strict
        /\
        hasPowerAt t3_strict
        /\
        shutterButtonPressedAt t3_strict
        /\
        apertureSettingAt as1 t3_strict
        ->
        (forall d : T, d in [t3_strict, t3_strict + ShutterTime ss_strict] -> apertureContractedAt d)
    )
    as1_strict
.
all_e (forall (ss:SS) (as1 : AS),
        shutterSettingAt ss t3_strict
        /\
        hasPowerAt t3_strict
        /\
        shutterButtonPressedAt t3_strict
        /\
        apertureSettingAt as1 t3_strict
        ->
        (forall d : T, d in [t3_strict, t3_strict + ShutterTime ss] -> apertureContractedAt d)
    )
    ss_strict
.
all_e (forall (t:T) (ss:SS) (as1 : AS),
        shutterSettingAt ss t 
        /\
        hasPowerAt t
        /\
        shutterButtonPressedAt t
        /\
        apertureSettingAt as1 t
        ->
        (forall d : T, d in [t, t + ShutterTime ss] -> apertureContractedAt d)
    )
    t3_strict
.

hyp H2.
con_i.
hyp a_shutter_setting.
con_i.
hyp a_has_power.
con_i.
hyp H17.
hyp a_aperture_setting.
interval.
imp_e (t3_strict <= i_strict /\ i_strict < t3_strict + ShutterTime ss_strict).
imp_i ab2.
con_i.
con_e1 (i_strict < t3_strict + ShutterTime ss_strict).
hyp ab2.
imp_e (i_strict < t3_strict + ShutterTime ss_strict).
imp_i abc1.
lin_solve.
con_e2 (t3_strict <= i_strict).
hyp ab2.
hyp ab1.

(*=========focussedlenslightat======*)
imp_e (focusSettingAt fs_strict i_strict /\ visualWorldStateInScopeAt i_strict).
all_e (forall (fs : FS),
        focusSettingAt fs i_strict
        /\
        visualWorldStateInScopeAt i_strict
        ->
        focussedLensLightAt i_strict
    )
    fs_strict
.
all_e (forall (t : T) (fs : FS), focusSettingAt fs t /\ visualWorldStateInScopeAt t -> focussedLensLightAt t) i_strict.
hyp H0.
con_i.
exi_e (exists d:T, y2_strict + d = i_strict) d2_strict ab3.
exi_i (i_strict - y2_strict).
lin_solve.

replace i_strict with (y2_strict + d2_strict).

imp_e (
    d2_strict >= 0
    /\
    (forall fs2 : FS,
        fs_strict <> fs2
        ->
        forall x : T,
        x in [y2_strict, (y2_strict + d2_strict)]
                ->
                ~ focusSelectorTurnedToAt fs2 x)
)
.
all_e (forall d : T,
        d >= 0
        /\
        (forall fs2 : FS,
            fs_strict <> fs2
            ->
            forall x : T,
                x in [y2_strict, y2_strict + d]
                    -> ~ focusSelectorTurnedToAt fs2 x)
        ->
        focusSettingAt fs_strict (y2_strict + d)
    )
    d2_strict
.
imp_e (focusSelectorTurnedToAt fs_strict y2_strict).
all_e (forall (fs : FS),
        focusSelectorTurnedToAt fs y2_strict
        ->
        (
            forall d: T,
            d >= 0
            (* possibly replace by t2 where t2 = t+d ?????????????????????????????*)
            /\
            (
                forall fs2 : FS,
                fs <> fs2
                ->
                (
                    forall x: T,
                    x in [y2_strict, y2_strict + d]
                            ->
                            ~ focusSelectorTurnedToAt fs2 x
                )
            )
            ->
            focusSettingAt fs (y2_strict + d)
        )
    )
    fs_strict
.
all_e (forall (t : T) (fs : FS),
        focusSelectorTurnedToAt fs t
        ->
        (
            forall d: T,
            d >= 0
            (* possibly replace by t2 where t2 = t+d ?????????????????????????????*)
            /\
            (
                forall fs2 : FS,
                fs <> fs2
                ->
                (
                    forall x: T,
                    x in [t, t + d]
                            ->
                            ~ focusSelectorTurnedToAt fs2 x
                )
            )
            ->
            focusSettingAt fs (t + d)
        )
    )
    y2_strict
.
hyp H7.
hyp H21.
con_i.
replace d2_strict with (i_strict - y2_strict).
imp_e (i_strict >= y2_strict).
imp_i ab4.
lin_solve.
imp_e (t3_strict <= i_strict /\  y2_strict <= t3_strict).
imp_i ab4.
imp_e (t3_strict <= i_strict).
imp_i ab5.
imp_e (y2_strict <= t3_strict).
imp_i ab6.
lin_solve.
con_e2 (t3_strict <= i_strict).
hyp ab4.
con_e1 (y2_strict <= t3_strict).
hyp ab4.
con_i.
con_e1 (i_strict < t3_strict + ShutterTime ss_strict).
hyp ab1.
imp_e (y2_strict < t3_strict).
imp_i ab4.
lin_solve.
con_e2 (t2_strict <= y2_strict).
hyp H20.
replace i_strict with (y2_strict + d2_strict).
lin_solve.
all_i fs2_strict.
imp_i ab5.
all_i x_strict.
imp_i ab6.
imp_e (fs_strict <> fs2_strict).
all_e (forall fs2 : FS, fs_strict <> fs2 -> ~ focusSelectorTurnedToAt fs2 x_strict) fs2_strict.
con_e2 (forall ss2 : SS, ss_strict <> ss2 -> ~ shutterSelectorTurnedToAt ss2 x_strict).
con_e2 (forall as2 : AS, as1_strict <> as2 -> ~ apertureSelectorTurnedToAt as2 x_strict).
imp_e (x_strict in [t1_strict, t3_strict + ShutterTime ss_strict]).
all_e (forall t : T,
        t in [t1_strict, t3_strict + ShutterTime ss_strict] ->
                (forall as2 : AS, as1_strict <> as2 -> ~ apertureSelectorTurnedToAt as2 t)
                /\
                (forall ss2 : SS, ss_strict <> ss2 -> ~ shutterSelectorTurnedToAt ss2 t)
                /\
                (forall fs2 : FS, fs_strict <> fs2 -> ~ focusSelectorTurnedToAt fs2 t)
    ) x_strict.
hyp H12.
interval.
imp_e (y2_strict <= x_strict /\ x_strict <= y2_strict + d2_strict).
imp_i ab7.
imp_e (t3_strict <= i_strict /\ i_strict <  t3_strict + ShutterTime ss_strict).
imp_i ab8.
imp_e (t2_strict <= y2_strict /\ y2_strict < t3_strict).
imp_i ab9.
imp_e (t2_strict <= y2_strict).
imp_i ab10.
imp_e (y2_strict <= x_strict).
imp_i ab11.
imp_e (x_strict <= y2_strict + d2_strict).
imp_i ab12.
imp_e (t3_strict <= i_strict /\ i_strict < t3_strict + ShutterTime ss_strict).
imp_i ab13.
imp_e (i_strict < t3_strict + ShutterTime ss_strict).
imp_i ab14.
con_i.
lin_solve.
lin_solve.
con_e2 (t3_strict <= i_strict).
hyp ab8.
hyp ab1.
con_e2 (y2_strict <= x_strict).
hyp ab7.
con_e1 (x_strict <= y2_strict + d2_strict).
hyp ab6.
con_e1 (y2_strict < t3_strict).
hyp ab9.
hyp H20.
hyp ab1.
hyp ab6.
hyp ab5.
imp_e (i_strict in [t3_strict, t3_strict + ShutterTime ss_strict)).
all_e (forall y3 : T, y3 in [t3_strict, t3_strict + ShutterTime ss_strict) -> visualWorldStateInScopeAt y3) i_strict.
hyp H16.
hyp ab1.

(*==============haspowerat===============*)

exi_e (exists d3:T, y1_strict + d3 = t3_strict) d3_strict ab1.
exi_i (t3_strict - y1_strict).
lin_solve.
replace t3_strict with (y1_strict + d3_strict).
imp_e ((y1_strict + d3_strict) in [y1_strict, t3_strict]).
all_e (forall i : T, i in [y1_strict, t3_strict] -> hasPowerAt i) (y1_strict + d3_strict).
imp_e (shutterButtonPressedAt (y1_strict + d3_strict)
        /\
        d3_strict > 0
        /\
        (forall d2 : T, d2 in [y1_strict, (y1_strict + d3_strict)) -> ~ shutterButtonPressedAt d2))
.
replace t3_strict with (y1_strict + d3_strict).
all_e ( forall d : T,
        shutterButtonPressedAt (y1_strict + d)
        /\
        d > 0
        /\
        (forall d2 : T,
            d2 in [y1_strict, y1_strict + d)
                    ->
                    ~ shutterButtonPressedAt d2)
        ->
        (
            forall i : T,
            i in [y1_strict, y1_strict + d]
                    ->
                    hasPowerAt i
        )
    )
    d3_strict
.
imp_e (leverPulledAt y1_strict).
all_e (forall t : T,
    leverPulledAt t ->
    forall d : T,
    shutterButtonPressedAt (t + d) /\ d > 0 /\ (forall d2 : T, d2 in [t, t + d) -> ~ shutterButtonPressedAt d2) ->
    forall i : T, i in [t, t + d] -> hasPowerAt i)
    y1_strict
.
hyp H.
hyp H19.
con_i.
replace (y1_strict + d3_strict) with t3_strict.
hyp H17.
con_i.
imp_e (t1_strict <= y1_strict /\ y1_strict < t2_strict).
imp_i ab2.
imp_e (y1_strict < t2_strict).
imp_i ab4.
lin_solve.
con_e2 (t1_strict <= y1_strict).
hyp ab2.
hyp H18.
all_i d2_strict.
imp_i ab2.
imp_e (d2_strict in [t1_strict, t3_strict)).
all_e (forall t : T, t in [t1_strict, t3_strict) -> ~ shutterButtonPressedAt t) d2_strict.
hyp H14.
interval.
(*need ab2, H18, *)
imp_e (y1_strict <= d2_strict /\ d2_strict < y1_strict + d3_strict).
imp_i ab3.
imp_e (t1_strict <= y1_strict /\ y1_strict < t2_strict).
imp_i ab4.
imp_e (y1_strict <= d2_strict).
imp_i ab5.
imp_e (t1_strict <= y1_strict).
imp_i ab6.
imp_e (d2_strict < y1_strict + d3_strict).
imp_i ab7.
con_i.
lin_solve.
replace t3_strict with (y1_strict + d3_strict).
lin_solve.
con_e2 (y1_strict <= d2_strict).
hyp ab3.
con_e1 (y1_strict < t2_strict).
hyp ab4.
con_e1 (d2_strict < y1_strict + d3_strict).
hyp ab3.
hyp H18.
hyp ab2.
replace (y1_strict + d3_strict) with t3_strict.
imp_e (t1_strict <= y1_strict /\ y1_strict < t2_strict).
imp_i ab2.
interval.
con_i.
imp_e (y1_strict < t2_strict).
imp_i ab3.
lin_solve.
con_e2 (t1_strict <= y1_strict).
hyp ab2.
lin_solve.
hyp H18.


(* ======================= *)
(* SHUTTERSETTING *)
(* ======================= *)  


replace t3_strict with ((t3_strict - d_strict) + d_strict).
imp_e (
    d_strict >= 0
    /\
    (forall ss2 : SS,
        ss_strict <> ss2
        ->
        forall x : T,
        x in [(t3_strict - d_strict), (t3_strict - d_strict) + d_strict]
                ->
                ~ shutterSelectorTurnedToAt ss2 x)
)
.
all_e (forall d : T,
        d >= 0
        /\
        (forall ss2 : SS,
            ss_strict <> ss2
            ->
            forall x : T,
                x in [(t3_strict - d_strict), (t3_strict - d_strict) + d]
                    -> ~ shutterSelectorTurnedToAt ss2 x)
        ->
        shutterSettingAt ss_strict ((t3_strict - d_strict) + d)
    )
    d_strict
.
imp_e (shutterSelectorTurnedToAt ss_strict (t3_strict - d_strict)).
all_e (forall (ss : SS),
        shutterSelectorTurnedToAt ss (t3_strict - d_strict)
        ->
        (
            forall d: T,
            d >= 0
            (* possibly replace by t2 where t2 = t+d ?????????????????????????????*)
            /\
            (
                forall ss2 : SS,
                ss <> ss2
                ->
                (
                    forall x: T,
                    x in [(t3_strict - d_strict), (t3_strict - d_strict) + d]
                            ->
                            ~ shutterSelectorTurnedToAt ss2 x
                )
            )
            ->
            shutterSettingAt ss ((t3_strict - d_strict) + d)
        )
    )
    ss_strict
.
all_e (forall (t : T) (ss : SS),
        shutterSelectorTurnedToAt ss t
        ->
        (
            forall d: T,
            d >= 0
            (* possibly replace by t2 where t2 = t+d ?????????????????????????????*)
            /\
            (
                forall ss2 : SS,
                ss <> ss2
                ->
                (
                    forall x: T,
                    x in [t, t + d]
                            ->
                            ~ shutterSelectorTurnedToAt ss2 x
                )
            )
            ->
            shutterSettingAt ss (t + d)
        )
    )
    (t3_strict - d_strict)
.
hyp H5.
replace (t3_strict - d_strict) with y2_strict.
hyp H23.
replace d_strict with (t3_strict - y2_strict).
lin_solve.
con_i.
replace d_strict with (t3_strict - y2_strict).
imp_e (t2_strict <= y2_strict /\ y2_strict < t3_strict).
imp_i a6.
imp_e (t2_strict <= y2_strict).
imp_i ab7.
imp_e (y2_strict < t3_strict).
imp_i ab8.
lin_solve.
con_e2 (t2_strict <= y2_strict).
hyp a6.
con_e1 (y2_strict < t3_strict).
hyp a6.
hyp H20.
replace (t3_strict - d_strict + d_strict) with t3_strict.
replace (t3_strict - d_strict) with y2_strict.
all_i ss2_strict.
imp_i a7.
all_i x_strict.
imp_i a8.
imp_e (ss_strict <> ss2_strict).
all_e (forall ss2 : SS, ss_strict <> ss2 -> ~ shutterSelectorTurnedToAt ss2 x_strict) ss2_strict.
con_e1 (forall fs2 : FS, fs_strict <> fs2 -> ~ focusSelectorTurnedToAt fs2 x_strict).
con_e2 (forall as2 : AS, as1_strict <> as2 -> ~ apertureSelectorTurnedToAt as2 x_strict).
imp_e (x_strict in [t1_strict, t3_strict + ShutterTime ss_strict]).
all_e (forall t : T,
        t in [t1_strict, t3_strict + ShutterTime ss_strict] ->
                (forall as2 : AS, as1_strict <> as2 -> ~ apertureSelectorTurnedToAt as2 t)
                /\
                (forall ss2 : SS, ss_strict <> ss2 -> ~ shutterSelectorTurnedToAt ss2 t)
                /\
                (forall fs2 : FS, fs_strict <> fs2 -> ~ focusSelectorTurnedToAt fs2 t)
    ) x_strict.
hyp H12.

interval.
imp_e (y2_strict <= x_strict /\ x_strict <= t3_strict).
imp_i ab7.
imp_e (t2_strict <= y2_strict /\ y2_strict < t3_strict).
imp_i ab9.
imp_e (t2_strict <= y2_strict).
imp_i ab10.
imp_e (y2_strict <= x_strict).
imp_i ab11.
imp_e (x_strict <= t3_strict).
imp_i ab12.
imp_e (x_strict < t3_strict + ShutterTime ss_strict).
imp_i ab14.
con_i.
lin_solve.
lin_solve.
lin_solve.
con_e2 (y2_strict <= x_strict).
hyp ab7.
con_e1 (x_strict <= t3_strict).
hyp a8.
con_e1 (y2_strict < t3_strict).
hyp ab9.
hyp H20.
hyp a8.
hyp a7.
replace d_strict with (t3_strict - y2_strict).
lin_solve.
lin_solve.
lin_solve.


(* =========================================== *)
(* FOCUSSETTING *)
(* =========================================== *)


replace t3_strict with ((t3_strict - d_strict) + d_strict).
imp_e (
    d_strict >= 0
    /\
    (forall fs2 : FS,
        fs_strict <> fs2
        ->
        forall x : T,
        x in [(t3_strict - d_strict), (t3_strict - d_strict) + d_strict]
                ->
                ~ focusSelectorTurnedToAt fs2 x)
)
.
all_e (forall d : T,
        d >= 0
        /\
        (forall fs2 : FS,
            fs_strict <> fs2
            ->
            forall x : T,
                x in [(t3_strict - d_strict), (t3_strict - d_strict) + d]
                    -> ~ focusSelectorTurnedToAt fs2 x)
        ->
        focusSettingAt fs_strict ((t3_strict - d_strict) + d)
    )
    d_strict
.
imp_e (focusSelectorTurnedToAt fs_strict (t3_strict - d_strict)).
all_e (forall (fs : FS),
        focusSelectorTurnedToAt fs (t3_strict - d_strict)
        ->
        (
            forall d: T,
            d >= 0
            (* possibly replace by t2 where t2 = t+d ?????????????????????????????*)
            /\
            (
                forall fs2 : FS,
                fs <> fs2
                ->
                (
                    forall x: T,
                    x in [(t3_strict - d_strict), (t3_strict - d_strict) + d]
                            ->
                            ~ focusSelectorTurnedToAt fs2 x
                )
            )
            ->
            focusSettingAt fs ((t3_strict - d_strict) + d)
        )
    )
    fs_strict
.
all_e (forall (t : T) (fs : FS),
        focusSelectorTurnedToAt fs t
        ->
        (
            forall d: T,
            d >= 0
            (* possibly replace by t2 where t2 = t+d ?????????????????????????????*)
            /\
            (
                forall fs2 : FS,
                fs <> fs2
                ->
                (
                    forall x: T,
                    x in [t, t + d]
                            ->
                            ~ focusSelectorTurnedToAt fs2 x
                )
            )
            ->
            focusSettingAt fs (t + d)
        )
    )
    (t3_strict - d_strict)
.
hyp H7.
replace (t3_strict - d_strict) with y2_strict.
hyp H21.
replace d_strict with (t3_strict - y2_strict).
lin_solve.
con_i.
replace d_strict with (t3_strict - y2_strict).
imp_e (t2_strict <= y2_strict /\ y2_strict < t3_strict).
imp_i a6.
imp_e (t2_strict <= y2_strict).
imp_i ab7.
imp_e (y2_strict < t3_strict).
imp_i ab8.
lin_solve.
con_e2 (t2_strict <= y2_strict).
hyp a6.
con_e1 (y2_strict < t3_strict).
hyp a6.
hyp H20.
replace (t3_strict - d_strict + d_strict) with t3_strict.
replace (t3_strict - d_strict) with y2_strict.
all_i fs2_strict.
imp_i a7.
all_i x_strict.
imp_i a8.
imp_e (fs_strict <> fs2_strict).
all_e (forall fs2 : FS, fs_strict <> fs2 -> ~ focusSelectorTurnedToAt fs2 x_strict) fs2_strict.
con_e2 (forall ss2 : SS, ss_strict <> ss2 -> ~ shutterSelectorTurnedToAt ss2 x_strict).
con_e2 (forall as2 : AS, as1_strict <> as2 -> ~ apertureSelectorTurnedToAt as2 x_strict).
imp_e (x_strict in [t1_strict, t3_strict + ShutterTime ss_strict]).
all_e (forall t : T,
        t in [t1_strict, t3_strict + ShutterTime ss_strict] ->
                (forall as2 : AS, as1_strict <> as2 -> ~ apertureSelectorTurnedToAt as2 t)
                /\
                (forall ss2 : SS, ss_strict <> ss2 -> ~ shutterSelectorTurnedToAt ss2 t)
                /\
                (forall fs2 : FS, fs_strict <> fs2 -> ~ focusSelectorTurnedToAt fs2 t)
    ) x_strict.
hyp H12.

interval.
imp_e (y2_strict <= x_strict /\ x_strict <= t3_strict).
imp_i ab7.
imp_e (t2_strict <= y2_strict /\ y2_strict < t3_strict).
imp_i ab9.
imp_e (t2_strict <= y2_strict).
imp_i ab10.
imp_e (y2_strict <= x_strict).
imp_i ab11.
imp_e (x_strict <= t3_strict).
imp_i ab12.
imp_e (x_strict < t3_strict + ShutterTime ss_strict).
imp_i ab14.
con_i.
lin_solve.
lin_solve.
lin_solve.
con_e2 (y2_strict <= x_strict).
hyp ab7.
con_e1 (x_strict <= t3_strict).
hyp a8.
con_e1 (y2_strict < t3_strict).
hyp ab9.
hyp H20.
hyp a8.
hyp a7.
replace d_strict with (t3_strict - y2_strict).
lin_solve.
lin_solve.
lin_solve.


(* =========================================== *)
(* APERTURESETTING *)
(* =========================================== *)


replace t3_strict with ((t3_strict - d_strict) + d_strict).
imp_e (
    d_strict >= 0
    /\
    (forall as2 : AS,
        as1_strict <> as2
        ->
        forall x : T,
        x in [(t3_strict - d_strict), (t3_strict - d_strict) + d_strict]
                ->
                ~ apertureSelectorTurnedToAt as2 x)
)
.
all_e (forall d : T,
        d >= 0
        /\
        (forall as2 : AS,
            as1_strict <> as2
            ->
            forall x : T,
                x in [(t3_strict - d_strict), (t3_strict - d_strict) + d]
                    -> ~ apertureSelectorTurnedToAt as2 x)
        ->
        apertureSettingAt as1_strict ((t3_strict - d_strict) + d)
    )
    d_strict
.
imp_e (apertureSelectorTurnedToAt as1_strict (t3_strict - d_strict)).
all_e (forall (as1 : AS),
        apertureSelectorTurnedToAt as1 (t3_strict - d_strict)
        ->
        (
            forall d: T,
            d >= 0
            (* possibly replace by t2 where t2 = t+d ?????????????????????????????*)
            /\
            (
                forall as2 : AS,
                as1 <> as2
                ->
                (
                    forall x: T,
                    x in [(t3_strict - d_strict), (t3_strict - d_strict) + d]
                            ->
                            ~ apertureSelectorTurnedToAt as2 x
                )
            )
            ->
            apertureSettingAt as1 ((t3_strict - d_strict) + d)
        )
    )
    as1_strict
.
all_e (forall (t : T) (as1 : AS),
        apertureSelectorTurnedToAt as1 t
        ->
        (
            forall d: T,
            d >= 0
            (* possibly replace by t2 where t2 = t+d ?????????????????????????????*)
            /\
            (
                forall as2 : AS,
                as1 <> as2
                ->
                (
                    forall x: T,
                    x in [t, t + d]
                            ->
                            ~ apertureSelectorTurnedToAt as2 x
                )
            )
            ->
            apertureSettingAt as1 (t + d)
        )
    )
    (t3_strict - d_strict)
.
hyp H6.
replace (t3_strict - d_strict) with y2_strict.
hyp H22.
replace d_strict with (t3_strict - y2_strict).
lin_solve.
con_i.
replace d_strict with (t3_strict - y2_strict).
imp_e (t2_strict <= y2_strict /\ y2_strict < t3_strict).
imp_i a6.
imp_e (t2_strict <= y2_strict).
imp_i ab7.
imp_e (y2_strict < t3_strict).
imp_i ab8.
lin_solve.
con_e2 (t2_strict <= y2_strict).
hyp a6.
con_e1 (y2_strict < t3_strict).
hyp a6.
hyp H20.
replace (t3_strict - d_strict + d_strict) with t3_strict.
replace (t3_strict - d_strict) with y2_strict.
all_i as2_strict.
imp_i a7.
all_i x_strict.
imp_i a8.
imp_e (as1_strict <> as2_strict).
all_e (forall as2 : AS, as1_strict <> as2 -> ~ apertureSelectorTurnedToAt as2 x_strict) as2_strict.
con_e1 ((forall ss2 : SS, ss_strict <> ss2 -> ~ shutterSelectorTurnedToAt ss2 x_strict)
        /\
        (forall fs2 : FS, fs_strict <> fs2 -> ~ focusSelectorTurnedToAt fs2 x_strict)
        )
.
imp_e (x_strict in [t1_strict, t3_strict + ShutterTime ss_strict]).
all_e (forall t : T,
        t in [t1_strict, t3_strict + ShutterTime ss_strict] ->
                (forall as2 : AS, as1_strict <> as2 -> ~ apertureSelectorTurnedToAt as2 t)
                /\
                (forall ss2 : SS, ss_strict <> ss2 -> ~ shutterSelectorTurnedToAt ss2 t)
                /\
                (forall fs2 : FS, fs_strict <> fs2 -> ~ focusSelectorTurnedToAt fs2 t)
    ) x_strict.
hyp H12.

interval.
imp_e (y2_strict <= x_strict /\ x_strict <= t3_strict).
imp_i ab7.
imp_e (t2_strict <= y2_strict /\ y2_strict < t3_strict).
imp_i ab9.
imp_e (t2_strict <= y2_strict).
imp_i ab10.
imp_e (y2_strict <= x_strict).
imp_i ab11.
imp_e (x_strict <= t3_strict).
imp_i ab12.
imp_e (x_strict < t3_strict + ShutterTime ss_strict).
imp_i ab14.
con_i.
lin_solve.
lin_solve.
lin_solve.
con_e2 (y2_strict <= x_strict).
hyp ab7.
con_e1 (x_strict <= t3_strict).
hyp a8.
con_e1 (y2_strict < t3_strict).
hyp ab9.
hyp H20.
hyp a8.
hyp a7.
replace d_strict with (t3_strict - y2_strict).
lin_solve.
lin_solve.
lin_solve.
Qed.

