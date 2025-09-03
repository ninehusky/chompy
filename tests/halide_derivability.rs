use ruler::{
    conditions::{
        assumption::Assumption, implication::Implication, implication_set::ImplicationSet,
    },
    enumo::{build_pvec_to_patterns, Rule, Ruleset, Workload},
    halide::Pred,
    Limits, SynthLanguage,
};

struct DerivabilityResult<L: SynthLanguage> {
    can: Ruleset<L>,
    cannot: Ruleset<L>,
}

// Grabbed using the script in python/halide_to_chompy.py.
const HALIDE_RULES: &str = r#"
(< (* x c0) (* y c0)) ==> (< x y) if (> c0 0)
(< (* x c0) (* y c0)) ==> (< y x) if (< c0 0)
(< (/ x c0) c1) ==> (< x (* c1 c0)) if (> c0 0)
(< (min z y) (min x (+ y c0))) ==> (< (min z y) x) if (> c0 0)
(< (min z y) (min (+ y c0) x)) ==> (< (min z y) x) if (> c0 0)
(< (min z (+ y c0)) (min x y)) ==> (< (min z (+ y c0)) x) if (< c0 0)
(< (min z (+ y c0)) (min y x)) ==> (< (min z (+ y c0)) x) if (< c0 0)
(< (min y z) (min x (+ y c0))) ==> (< (min z y) x) if (> c0 0)
(< (min y z) (min (+ y c0) x)) ==> (< (min z y) x) if (> c0 0)
(< (min (+ y c0) z) (min x y)) ==> (< (min z (+ y c0)) x) if (< c0 0)
(< (min (+ y c0) z) (min y x)) ==> (< (min z (+ y c0)) x) if (< c0 0)
(< (max z y) (max x (+ y c0))) ==> (< (max z y) x) if (< c0 0)
(< (max z y) (max (+ y c0) x)) ==> (< (max z y) x) if (< c0 0)
(< (max z (+ y c0)) (max x y)) ==> (< (max z (+ y c0)) x) if (> c0 0)
(< (max z (+ y c0)) (max y x)) ==> (< (max z (+ y c0)) x) if (> c0 0)
(< (max y z) (max x (+ y c0))) ==> (< (max z y) x) if (< c0 0)
(< (max y z) (max (+ y c0) x)) ==> (< (max z y) x) if (< c0 0)
(< (max (+ y c0) z) (max x y)) ==> (< (max z (+ y c0)) x) if (> c0 0)
(< (max (+ y c0) z) (max y x)) ==> (< (max z (+ y c0)) x) if (> c0 0)
(< x (select y (+ x c0) z)) ==> (! (&& y (< x z))) if (<= c0 0)
(< x (select y (+ x c0) z)) ==> (|| y (< x z)) if (> c0 0)
(< x (select y z (+ x c0))) ==> (&& y (< x z)) if (<= c0 0)
(< x (select y z (+ x c0))) ==> (! (|| y (< x z))) if (> c0 0)
(< x (+ (select y (+ x c0) z) c1)) ==> (! (&& y (< x (+ z c1)))) if (<= (+ c0 c1) 0)
(< x (+ (select y (+ x c0) z) c1)) ==> (|| y (< x (+ z c1))) if (> (+ c0 c1) 0)
(< x (+ (select y z (+ x c0)) c1)) ==> (&& y (< x (+ z c1))) if (<= (+ c0 c1) 0)
(< x (+ (select y z (+ x c0)) c1)) ==> (! (|| y (< x (+ z c1)))) if (> (+ c0 c1) 0)
(< (select y (+ x c0) z) x) ==> (! (&& y (< z x))) if (>= c0 0)
(< (select y (+ x c0) z) x) ==> (|| y (< z x)) if (< c0 0)
(< (select y z (+ x c0)) x) ==> (&& y (< z x)) if (>= c0 0)
(< (select y z (+ x c0)) x) ==> (! (|| y (< z x))) if (< c0 0)
(< (select y (+ x c0) z) (+ x c1)) ==> (! (&& y (< z (+ x c1)))) if (>= c0 c1)
(< (select y (+ x c0) z) (+ x c1)) ==> (|| y (< z (+ x c1))) if (< c0 c1)
(< (select y z (+ x c0)) (+ x c1)) ==> (&& y (< z (+ x c1))) if (>= c0 c1)
(< (select y z (+ x c0)) (+ x c1)) ==> (! (|| y (< z (+ x c1)))) if (< c0 c1)
(< x (* (/ x c1) c1)) ==> 0 if (> c1 0)
(< (/ (+ x c1) c0) (/ (+ x c2) c0)) ==> 0 if (> c0 (&& 0 (>= c1 c2)))
(< (/ (+ x c1) c0) (/ (+ x c2) c0)) ==> 1 if (> c0 (&& 0 (<= c1 (- c2 c0))))
(< (/ x c0) (/ (+ x c2) c0)) ==> 0 if (> c0 (&& 0 (>= 0 c2)))
(< (/ x c0) (/ (+ x c2) c0)) ==> 1 if (> c0 (&& 0 (<= 0 (- c2 c0))))
(< (/ (+ x c1) c0) (/ x c0)) ==> 0 if (> c0 (&& 0 (>= c1 0)))
(< (/ (+ x c1) c0) (/ x c0)) ==> 1 if (> c0 (&& 0 (<= c1 (- 0 c0))))
(< (/ (+ x c1) c0) (+ (/ x c0) c2)) ==> 0 if (> c0 (&& 0 (>= c1 (* c2 c0))))
(< (/ (+ x c1) c0) (+ (/ x c0) c2)) ==> 1 if (> c0 (&& 0 (<= c1 (- (* c2 c0) c0))))
(< (/ (+ x c1) c0) (+ (min (/ x c0) y) c2)) ==> 0 if (> c0 (&& 0 (>= c1 (* c2 c0))))
(< (/ (+ x c1) c0) (+ (max (/ x c0) y) c2)) ==> 1 if (> c0 (&& 0 (<= c1 (- (* c2 c0) c0))))
(< (/ (+ x c1) c0) (min (/ (+ x c2) c0) y)) ==> 0 if (> c0 (&& 0 (>= c1 c2)))
(< (/ (+ x c1) c0) (max (/ (+ x c2) c0) y)) ==> 1 if (> c0 (&& 0 (<= c1 (- c2 c0))))
(< (/ (+ x c1) c0) (min (/ x c0) y)) ==> 0 if (> c0 (&& 0 (>= c1 0)))
(< (/ (+ x c1) c0) (max (/ x c0) y)) ==> 1 if (> c0 (&& 0 (<= c1 (- 0 c0))))
(< (/ (+ x c1) c0) (+ (min y (/ x c0)) c2)) ==> 0 if (> c0 (&& 0 (>= c1 (* c2 c0))))
(< (/ (+ x c1) c0) (+ (max y (/ x c0)) c2)) ==> 1 if (> c0 (&& 0 (<= c1 (- (* c2 c0) c0))))
(< (/ (+ x c1) c0) (min y (/ (+ x c2) c0))) ==> 0 if (> c0 (&& 0 (>= c1 c2)))
(< (/ (+ x c1) c0) (max y (/ (+ x c2) c0))) ==> 1 if (> c0 (&& 0 (<= c1 (- c2 c0))))
(< (/ (+ x c1) c0) (min y (/ x c0))) ==> 0 if (> c0 (&& 0 (>= c1 0)))
(< (/ (+ x c1) c0) (max y (/ x c0))) ==> 1 if (> c0 (&& 0 (<= c1 (- 0 c0))))
(< (max (/ (+ x c2) c0) y) (/ (+ x c1) c0)) ==> 0 if (> c0 (&& 0 (>= c2 c1)))
(< (min (/ (+ x c2) c0) y) (/ (+ x c1) c0)) ==> 1 if (> c0 (&& 0 (<= c2 (- c1 c0))))
(< (max (/ x c0) y) (/ (+ x c1) c0)) ==> 0 if (> c0 (&& 0 (>= 0 c1)))
(< (min (/ x c0) y) (/ (+ x c1) c0)) ==> 1 if (> c0 (&& 0 (<= 0 (- c1 c0))))
(< (max y (/ (+ x c2) c0)) (/ (+ x c1) c0)) ==> 0 if (> c0 (&& 0 (>= c2 c1)))
(< (min y (/ (+ x c2) c0)) (/ (+ x c1) c0)) ==> 1 if (> c0 (&& 0 (<= c2 (- c1 c0))))
(< (max y (/ x c0)) (/ (+ x c1) c0)) ==> 0 if (> c0 (&& 0 (>= 0 c1)))
(< (min y (/ x c0)) (/ (+ x c1) c0)) ==> 1 if (> c0 (&& 0 (<= 0 (- c1 c0))))
(< (max (/ (+ x c2) c0) y) (+ (/ x c0) c1)) ==> 0 if (> c0 (&& 0 (>= c2 (* c1 c0))))
(< (min (/ (+ x c2) c0) y) (+ (/ x c0) c1)) ==> 1 if (> c0 (&& 0 (<= c2 (- (* c1 c0) c0))))
(< (max y (/ (+ x c2) c0)) (+ (/ x c0) c1)) ==> 0 if (> c0 (&& 0 (>= c2 (* c1 c0))))
(< (min y (/ (+ x c2) c0)) (+ (/ x c0) c1)) ==> 1 if (> c0 (&& 0 (<= c2 (- (* c1 c0) c0))))
(< (/ x c0) (min (/ (+ x c2) c0) y)) ==> 0 if (> c0 (&& 0 (< c2 0)))
(< (/ x c0) (max (/ (+ x c2) c0) y)) ==> 1 if (> c0 (&& 0 (<= c0 c2)))
(< (/ x c0) (min y (/ (+ x c2) c0))) ==> 0 if (> c0 (&& 0 (< c2 0)))
(< (/ x c0) (max y (/ (+ x c2) c0))) ==> 1 if (> c0 (&& 0 (<= c0 c2)))
(< (max (/ (+ x c2) c0) y) (/ x c0)) ==> 0 if (> c0 (&& 0 (>= c2 0)))
(< (min (/ (+ x c2) c0) y) (/ x c0)) ==> 1 if (> c0 (&& 0 (<= (+ c2 c0) 0)))
(< (max y (/ (+ x c2) c0)) (/ x c0)) ==> 0 if (> c0 (&& 0 (>= c2 0)))
(< (min y (/ (+ x c2) c0)) (/ x c0)) ==> 1 if (> c0 (&& 0 (<= (+ c2 c0) 0)))
(< (/ (+ (max x (+ (* y c0) c1)) c2) c0) y) ==> (< (/ (+ x c2) c0) y) if (> c0 (&& 0 (< (+ c1 c2) 0)))
(< (/ (+ (max x (+ (* y c0) c1)) c2) c0) y) ==> 0 if (> c0 (&& 0 (>= (+ c1 c2) 0)))
(< (/ (+ (max x (* y c0)) c1) c0) y) ==> (< (/ (+ x c1) c0) y) if (> c0 (&& 0 (< c1 0)))
(< (/ (+ (max x (* y c0)) c1) c0) y) ==> 0 if (> c0 (&& 0 (>= c1 0)))
(< (/ (+ (max (+ (* x c0) c1) y) c2) c0) x) ==> (< (/ (+ y c2) c0) x) if (> c0 (&& 0 (< (+ c1 c2) 0)))
(< (/ (+ (max (+ (* x c0) c1) y) c2) c0) x) ==> 0 if (> c0 (&& 0 (>= (+ c1 c2) 0)))
(< (/ (+ (max (* x c0) y) c1) c0) x) ==> (< (/ (+ y c1) c0) x) if (> c0 (&& 0 (< c1 0)))
(< (/ (+ (max (* x c0) y) c1) c0) x) ==> 0 if (> c0 (&& 0 (>= c1 0)))
(< (/ (max x (+ (* y c0) c1)) c0) y) ==> (< (/ x c0) y) if (> c0 (&& 0 (< c1 0)))
(< (/ (max x (+ (* y c0) c1)) c0) y) ==> 0 if (> c0 (&& 0 (>= c1 0)))
(< (/ (max x (* y c0)) c20) y) ==> 0 if (> c0 0)
(< (/ (max (+ (* x c0) c1) y) c0) x) ==> (< (/ y c0) x) if (> c0 (&& 0 (< c1 0)))
(< (/ (max (+ (* x c0) c1) y) c0) x) ==> 0 if (> c0 (&& 0 (>= c1 0)))
(< (/ (max (* x c0) y) c0) x) ==> 0 if (> c0 0)
(< (/ (+ (min x (+ (* y c0) c1)) c2) c0) y) ==> 1 if (> c0 (&& 0 (< (+ c1 c2) 0)))
(< (/ (+ (min x (+ (* y c0) c1)) c2) c0) y) ==> (< (/ (+ x c2) c0) y) if (> c0 (&& 0 (>= (+ c1 c2) 0)))
(< (/ (+ (min x (* y c0)) c1) c0) y) ==> 1 if (> c0 (&& 0 (< c1 0)))
(< (/ (+ (min x (* y c0)) c1) c0) y) ==> (< (/ (+ x c1) c0) y) if (> c0 (&& 0 (>= c1 0)))
(< (/ (+ (min (+ (* x c0) c1) y) c2) c0) x) ==> 1 if (> c0 (&& 0 (< (+ c1 c2) 0)))
(< (/ (+ (min (+ (* x c0) c1) y) c2) c0) x) ==> (< (/ (+ y c2) c0) x) if (> c0 (&& 0 (>= (+ c1 c2) 0)))
(< (/ (+ (min (* x c0) y) c1) c0) x) ==> 1 if (> c0 (&& 0 (< c1 0)))
(< (/ (+ (min (* x c0) y) c1) c0) x) ==> (< (/ (+ y c1) c0) x) if (> c0 (&& 0 (>= c1 0)))
(< (/ (min x (+ (* y c0) c1)) c0) y) ==> 1 if (> c0 (&& 0 (< c1 0)))
(< (/ (min x (+ (* y c0) c1)) c0) y) ==> (< (/ x c0) y) if (> c0 (&& 0 (>= c1 0)))
(< (/ (min x (* y c0)) c0) y) ==> (< (/ x c0) y) if (> c0 0)
(< (/ (min (+ (* x c0) c1) y) c0) x) ==> 1 if (> c0 (&& 0 (< c1 0)))
(< (/ (min (+ (* x c0) c1) y) c0) x) ==> (< (/ y c0) x) if (> c0 (&& 0 (>= c1 0)))
(< (/ (min (* x c0) y) c0) x) ==> (< (/ y c0) x) if (> c0 0)
(< (min x c0) (min x c1)) ==> 0 if (>= c0 c1)
(< (min x c0) (+ (min x c1) c2)) ==> 0 if (>= c0 (&& (+ c1 c2) (<= c2 0)))
(< (max x c0) (max x c1)) ==> 0 if (>= c0 c1)
(< (max x c0) (+ (max x c1) c2)) ==> 0 if (>= c0 (&& (+ c1 c2) (<= c2 0)))
(select (< 0 x) (min (* x c0) c1) (* x c0)) ==> (min (* x c0) c1) if (>= c1 (&& 0 (>= c0 0)))
(select (< x c0) 0 (+ (min x c0) c1)) ==> 0 if (== c0 (- c1))
(select (< 0 x) (/ (+ (* x c0) c1) x) y) ==> (select (< 0 x) (- c0 1) y) if (== c1 (- 1))
(select (< c0 x) (+ x c1) c2) ==> (max (+ x c1) c2) if (== c2 (|| (+ c0 c1) (== c2 (+ (+ c0 c1) 1))))
(select (< x c0) c1 (+ x c2)) ==> (max (+ x c2) c1) if (== c1 (|| (+ c0 c2) (== (+ c1 1) (+ c0 c2))))
(select (< c0 x) c1 (+ x c2)) ==> (min (+ x c2) c1) if (== c1 (|| (+ c0 c2) (== c1 (+ (+ c0 c2) 1))))
(select (< x c0) (+ x c1) c2) ==> (min (+ x c1) c2) if (== c2 (|| (+ c0 c1) (== (+ c2 1) (+ c0 c1))))
(select (< c0 x) x c1) ==> (max x c1) if (== c1 (+ c0 1))
(select (< x c0) c1 x) ==> (max x c1) if (== (+ c1 1) c0)
(select (< c0 x) c1 x) ==> (min x c1) if (== c1 (+ c0 1))
(select (< x c0) x c1) ==> (min x c1) if (== (+ c1 1) c0)
(max x c0) ==> b if (is_max_value c0)
(max x c0) ==> x if (is_min_value c0)
(max (* (/ x c0) c0) x) ==> b if (> c0 0)
(max x (* (/ x c0) c0)) ==> a if (> c0 0)
(max (min x c0) c1) ==> b if (>= c1 c0)
(max (+ (* (/ (+ x c0) c1) c1) c2) x) ==> a if (> c1 (&& 0 (>= (+ c0 c2) (- c1 1))))
(max x (+ (* (/ (+ x c0) c1) c1) c2)) ==> b if (> c1 (&& 0 (>= (+ c0 c2) (- c1 1))))
(max (+ (* (/ (+ x c0) c1) c1) c2) x) ==> b if (> c1 (&& 0 (<= (+ c0 c2) 0)))
(max x (+ (* (/ (+ x c0) c1) c1) c2)) ==> a if (> c1 (&& 0 (<= (+ c0 c2) 0)))
(max (* (/ x c0) c0) (+ (* (/ x c1) c1) c2)) ==> b if (>= c2 (&& c1 (> c1 (&& 0 (!= c0 0)))))
(max (+ (* (/ x c1) c1) c2) x) ==> a if (> c1 (&& 0 (>= c2 (- c1 1))))
(max x (+ (* (/ x c1) c1) c2)) ==> b if (> c1 (&& 0 (>= c2 (- c1 1))))
(max (* (/ (+ x c0) c1) c1) x) ==> a if (> c1 (&& 0 (>= c0 (- c1 1))))
(max x (* (/ (+ x c0) c1) c1)) ==> b if (> c1 (&& 0 (>= c0 (- c1 1))))
(max (+ (* (/ x c1) c1) c2) x) ==> b if (> c1 (&& 0 (<= c2 0)))
(max x (+ (* (/ x c1) c1) c2)) ==> a if (> c1 (&& 0 (<= c2 0)))
(max (* (/ (+ x c0) c1) c1) x) ==> b if (> c1 (&& 0 (<= c0 0)))
(max x (* (/ (+ x c0) c1) c1)) ==> a if (> c1 (&& 0 (<= c0 0)))
(max x (+ (min x y) c0)) ==> a if (<= c0 0)
(max x (+ (min y x) c0)) ==> a if (<= c0 0)
(max (+ (min x y) c0) x) ==> b if (<= c0 0)
(max (+ (min x y) c0) y) ==> b if (<= c0 0)
(max (min (- c0 x) x) c1) ==> b if (>= (* 2 c1) (- c0 1))
(max (min x (- c0 x)) c1) ==> b if (>= (* 2 c1) (- c0 1))
(max (max (/ x c0) y) (/ z c0)) ==> (max (/ (max x z) c0) y) if (> c0 0)
(max x (select (== x c0) c1 x)) ==> (select (== x c0) c1 x) if (< c0 c1)
(max x (select (== x c0) c1 x)) ==> x if (<= c1 c0)
(max (select (== x c0) c1 x) c2) ==> (max x c2) if (&& (<= c0 c2) (<= c1 c2))
(max (select (== x c0) c1 x) x) ==> (select (== x c0) c1 x) if (< c0 c1)
(max (select (== x c0) c1 x) x) ==> x if (<= c1 c0)
(max (+ (max x y) c0) x) ==> (max x (+ y c0)) if (< c0 0)
(max (+ (max x y) c0) x) ==> (+ (max x y) c0) if (> c0 0)
(max (+ (max y x) c0) x) ==> (max (+ y c0) x) if (< c0 0)
(max (+ (max y x) c0) x) ==> (+ (max y x) c0) if (> c0 0)
(max x (+ (max x y) c0)) ==> (max x (+ y c0)) if (< c0 0)
(max x (+ (max x y) c0)) ==> (+ (max x y) c0) if (> c0 0)
(max x (+ (max y x) c0)) ==> (max x (+ y c0)) if (< c0 0)
(max x (+ (max y x) c0)) ==> (+ (max x y) c0) if (> c0 0)
(max (max x y) (+ x c0)) ==> (max (+ x c0) y) if (> c0 0)
(max (max x y) (+ x c0)) ==> (max x y) if (< c0 0)
(max (max y x) (+ x c0)) ==> (max y (+ x c0)) if (> c0 0)
(max (max y x) (+ x c0)) ==> (max y x) if (< c0 0)
(max (* (+ (* x c0) y) c1) (+ (* x c2) z)) ==> (+ (max (* y c1) z) (* x c2)) if (== (* c0 c1) c2)
(max (* (+ y (* x c0)) c1) (+ (* x c2) z)) ==> (+ (max (* y c1) z) (* x c2)) if (== (* c0 c1) c2)
(max (* (+ (* x c0) y) c1) (+ z (* x c2))) ==> (+ (max (* y c1) z) (* x c2)) if (== (* c0 c1) c2)
(max (* (+ y (* x c0)) c1) (+ z (* x c2))) ==> (+ (max (* y c1) z) (* x c2)) if (== (* c0 c1) c2)
(max (/ x c0) (/ y c0)) ==> (/ (max x y) c0) if (> c0 0)
(max (/ x c0) (/ y c0)) ==> (/ (min x y) c0) if (< c0 0)
(max (* (/ (+ x c0) c1) c1) (+ x c2)) ==> (* (/ (+ x c0) c1) c1) if (> c1 (&& 0 (>= (+ c0 1) (+ c1 c2))))
(max (/ (+ x c0) c1) (* (/ (+ x c2) c3) c4)) ==> (/ (+ x c0) c1) if (<= c2 (&& c0 (> c1 (&& 0 (> c3 (&& 0 (== (* c1 c4) c3)))))))
(max (/ (+ x c0) c1) (* (/ (+ x c2) c3) c4)) ==> (* (/ (+ x c2) c3) c4) if (<= (- (+ c0 c3) c1) (&& c2 (> c1 (&& 0 (> c3 (&& 0 (== (* c1 c4) c3)))))))
(max (/ x c1) (* (/ (+ x c2) c3) c4)) ==> (/ x c1) if (<= c2 (&& 0 (> c1 (&& 0 (> c3 (&& 0 (== (* c1 c4) c3)))))))
(max (/ x c1) (* (/ (+ x c2) c3) c4)) ==> (* (/ (+ x c2) c3) c4) if (<= (- c3 c1) (&& c2 (> c1 (&& 0 (> c3 (&& 0 (== (* c1 c4) c3)))))))
(max (/ (+ x c0) c1) (* (/ x c3) c4)) ==> (/ (+ x c0) c1) if (<= 0 (&& c0 (> c1 (&& 0 (> c3 (&& 0 (== (* c1 c4) c3)))))))
(max (/ (+ x c0) c1) (* (/ x c3) c4)) ==> (* (/ x c3) c4) if (<= (- (+ c0 c3) c1) (&& 0 (> c1 (&& 0 (> c3 (&& 0 (== (* c1 c4) c3)))))))
(max (/ x c1) (* (/ x c3) c4)) ==> (/ x c1) if (> c1 (&& 0 (> c3 (&& 0 (== (* c1 c4) c3)))))
(== (select x c0 y) 0) ==> (! (&& x (== y 0))) if (!= c0 0)
(== (select x y c0) 0) ==> (&& x (== y 0)) if (!= c0 0)
(== (+ (max x c0) c1) 0) ==> 0 if (> (+ c0 c1) 0)
(== (+ (min x c0) c1) 0) ==> 0 if (< (+ c0 c1) 0)
(== (+ (max x c0) c1) 0) ==> (<= x c0) if (== (+ c0 c1) 0)
(== (+ (min x c0) c1) 0) ==> (<= c0 x) if (== (+ c0 c1) 0)
(== (max x c0) 0) ==> (== x 0) if (< c0 0)
(== (min x c0) 0) ==> (== x 0) if (> c0 0)
(== (max x c0) 0) ==> 0 if (> c0 0)
(== (min x c0) 0) ==> 0 if (< c0 0)
(/ (- (* x c1) y) c0) ==> (- (/ (- 0 y) c0) x) if (== (+ c0 c1) 0)
(/ (- (- (* x c1) y) z) c0) ==> (- (/ (- (- 0 y) z) c0) x) if (== (+ c0 c1) 0)
(!= x (&& c0 (== x c1))) ==> b if (!= c0 c1)
(== x (&& c0 (== x c1))) ==> 0 if (!= c0 c1)
(<= x (&& c1 (< c0 x))) ==> 0 if (<= c1 c0)
(<= c0 (&& x (< x c1))) ==> 0 if (<= c1 c0)
(<= c0 (&& x (<= x c1))) ==> 0 if (< c1 c0)
(<= x (&& c1 (<= c0 x))) ==> 0 if (< c1 c0)
(- (min x y) (min z w)) ==> (- y w) if (can_prove (== (- x y) (- z w)) this)
(- (min x y) (min w z)) ==> (- y w) if (can_prove (== (- x y) (- z w)) this)
(- (min (* x c0) c1) (* (min x c2) c0)) ==> (min (- c1 (* (min x c2) c0)) 0) if (> c0 (&& 0 (<= c1 (* c2 c0))))
(- (max x y) (max z w)) ==> (- y w) if (can_prove (== (- x y) (- z w)) this)
(- (max x y) (max w z)) ==> (- y w) if (can_prove (== (- x y) (- z w)) this)
(- (min x y) (min x w)) ==> (min (- y (min x w)) 0) if (can_prove (<= y w) this)
(- (min x y) (min x w)) ==> (max (- (min x y) w) 0) if (can_prove (>= y w) this)
(- (min (+ x c0) y) (min x w)) ==> (min (- y (min x w)) c0) if (can_prove (<= y (+ w c0)) this)
(- (min (+ x c0) y) (min x w)) ==> (max (- (min (+ x c0) y) w) c0) if (can_prove (>= y (+ w c0)) this)
(- (min y x) (min w x)) ==> (min (- y (min x w)) 0) if (can_prove (<= y w) this)
(- (min y x) (min w x)) ==> (max (- (min x y) w) 0) if (can_prove (>= y w) this)
(- (min y (+ x c0)) (min w x)) ==> (min (- y (min x w)) c0) if (can_prove (<= y (+ w c0)) this)
(- (min y (+ x c0)) (min w x)) ==> (max (- (min (+ x c0) y) w) c0) if (can_prove (>= y (+ w c0)) this)
(- (min x y) (min w x)) ==> (min (- y (min x w)) 0) if (can_prove (<= y w) this)
(- (min x y) (min w x)) ==> (max (- (min x y) w) 0) if (can_prove (>= y w) this)
(- (min (+ x c0) y) (min w x)) ==> (min (- y (min x w)) c0) if (can_prove (<= y (+ w c0)) this)
(- (min (+ x c0) y) (min w x)) ==> (max (- (min (+ x c0) y) w) c0) if (can_prove (>= y (+ w c0)) this)
(- (min y x) (min x w)) ==> (min (- y (min x w)) 0) if (can_prove (<= y w) this)
(- (min y x) (min x w)) ==> (max (- (min x y) w) 0) if (can_prove (>= y w) this)
(- (min y (+ x c0)) (min x w)) ==> (min (- y (min x w)) c0) if (can_prove (<= y (+ w c0)) this)
(- (min y (+ x c0)) (min x w)) ==> (max (- (min (+ x c0) y) w) c0) if (can_prove (>= y (+ w c0)) this)
(- (max x y) (max x w)) ==> (max (- y (max x w)) 0) if (can_prove (>= y w) this)
(- (max x y) (max x w)) ==> (min (- (max x y) w) 0) if (can_prove (<= y w) this)
(- (max (+ x c0) y) (max x w)) ==> (max (- y (max x w)) c0) if (can_prove (>= y (+ w c0)) this)
(- (max (+ x c0) y) (max x w)) ==> (min (- (max (+ x c0) y) w) c0) if (can_prove (<= y (+ w c0)) this)
(- (max y x) (max w x)) ==> (max (- y (max x w)) 0) if (can_prove (>= y w) this)
(- (max y x) (max w x)) ==> (min (- (max x y) w) 0) if (can_prove (<= y w) this)
(- (max y (+ x c0)) (max w x)) ==> (max (- y (max x w)) c0) if (can_prove (>= y (+ w c0)) this)
(- (max y (+ x c0)) (max w x)) ==> (min (- (max (+ x c0) y) w) c0) if (can_prove (<= y (+ w c0)) this)
(- (max x y) (max w x)) ==> (max (- y (max x w)) 0) if (can_prove (>= y w) this)
(- (max x y) (max w x)) ==> (min (- (max x y) w) 0) if (can_prove (<= y w) this)
(- (max (+ x c0) y) (max w x)) ==> (max (- y (max x w)) c0) if (can_prove (>= y (+ w c0)) this)
(- (max (+ x c0) y) (max w x)) ==> (min (- (max (+ x c0) y) w) c0) if (can_prove (<= y (+ w c0)) this)
(- (max y x) (max x w)) ==> (max (- y (max x w)) 0) if (can_prove (>= y w) this)
(- (max y x) (max x w)) ==> (min (- (max x y) w) 0) if (can_prove (<= y w) this)
(- (max y (+ x c0)) (max x w)) ==> (max (- y (max x w)) c0) if (can_prove (>= y (+ w c0)) this)
(- (max y (+ x c0)) (max x w)) ==> (min (- (max (+ x c0) y) w) c0) if (can_prove (<= y (+ w c0)) this)
(- (/ (+ (+ x y) z) c0) (/ (+ (+ y x) w) c0)) ==> (- (/ (+ (+ x y) z) c0) (/ (+ (+ x y) w) c0)) if (> c0 0)
(- (/ (+ x y) c0) (/ (+ y x) c0)) ==> 0 if (!= c0 0)
(- (/ (min (+ (* x c0) y) z) c1) (* x c2)) ==> (/ (min y (- z (* x c0))) c1) if (== c0 (* c1 c2))
(- (/ (min z (+ (* x c0) y)) c1) (* x c2)) ==> (/ (min y (- z (* x c0))) c1) if (== c0 (* c1 c2))
(- (/ (+ (min (+ (* x c0) y) z) w) c1) (* x c2)) ==> (/ (+ (min y (- z (* x c0))) w) c1) if (== c0 (* c1 c2))
(- (/ (+ (min z (+ (* x c0) y)) w) c1) (* x c2)) ==> (/ (+ (min (- z (* x c0)) y) w) c1) if (== c0 (* c1 c2))
(!= x (|| c0 (== x c1))) ==> a if (!= c0 c1)
(<= x (|| c0 (< c1 x))) ==> 1 if (<= c1 c0)
(<= c1 (|| x (< x c0))) ==> 1 if (<= c1 c0)
(< x (|| c0 (< c1 x))) ==> 1 if (< c1 c0)
(< c1 (|| x (< x c0))) ==> 1 if (< c1 c0)
(+ (select x y (+ z c0)) c1) ==> (select x (+ y c1) z) if (== (+ c0 c1) 0)
(+ (min x (+ y c0)) c1) ==> (min (+ x c1) y) if (== (+ c0 c1) 0)
(+ (min (+ y c0) x) c1) ==> (min y (+ x c1)) if (== (+ c0 c1) 0)
(+ (max x (+ y c0)) c1) ==> (max (+ x c1) y) if (== (+ c0 c1) 0)
(+ (max (+ y c0) x) c1) ==> (max y (+ x c1)) if (== (+ c0 c1) 0)
(+ (min x (+ y (* z c0))) (* z c1)) ==> (min (+ x (* z c1)) y) if (== (+ c0 c1) 0)
(+ (min x (+ (* y c0) z)) (* y c1)) ==> (min (+ x (* y c1)) z) if (== (+ c0 c1) 0)
(+ (min x (* y c0)) (* y c1)) ==> (min (+ x (* y c1)) 0) if (== (+ c0 c1) 0)
(+ (min (+ x (* y c0)) z) (* y c1)) ==> (min (+ (* y c1) z) x) if (== (+ c0 c1) 0)
(+ (min (+ (* x c0) y) z) (* x c1)) ==> (min y (+ (* x c1) z)) if (== (+ c0 c1) 0)
(+ (min (* x c0) y) (* x c1)) ==> (min (+ (* x c1) y) 0) if (== (+ c0 c1) 0)
(+ (max x (+ y (* z c0))) (* z c1)) ==> (max (+ x (* z c1)) y) if (== (+ c0 c1) 0)
(+ (max x (+ (* y c0) z)) (* y c1)) ==> (max (+ x (* y c1)) z) if (== (+ c0 c1) 0)
(+ (max x (* y c0)) (* y c1)) ==> (max (+ x (* y c1)) 0) if (== (+ c0 c1) 0)
(+ (max (+ x (* y c0)) z) (* y c1)) ==> (max x (+ (* y c1) z)) if (== (+ c0 c1) 0)
(+ (max (+ (* x c0) y) z) (* x c1)) ==> (max (+ (* x c1) z) y) if (== (+ c0 c1) 0)
(+ (max (* x c0) y) (* x c1)) ==> (max (+ (* x c1) y) 0) if (== (+ c0 c1) 0)
(min x c0) ==> b if (is_min_value c0)
(min x c0) ==> x if (is_max_value c0)
(min (* (/ x c0) c0) x) ==> a if (> c0 0)
(min x (* (/ x c0) c0)) ==> b if (> c0 0)
(min (max x c0) c1) ==> b if (<= c1 c0)
(min (+ (* (/ (+ x c0) c1) c1) c2) x) ==> b if (> c1 (&& 0 (>= (+ c0 c2) (- c1 1))))
(min x (+ (* (/ (+ x c0) c1) c1) c2)) ==> a if (> c1 (&& 0 (>= (+ c0 c2) (- c1 1))))
(min (+ (* (/ (+ x c0) c1) c1) c2) x) ==> a if (> c1 (&& 0 (<= (+ c0 c2) 0)))
(min x (+ (* (/ (+ x c0) c1) c1) c2)) ==> b if (> c1 (&& 0 (<= (+ c0 c2) 0)))
(min (* (/ x c0) c0) (+ (* (/ x c1) c1) c2)) ==> a if (>= c2 (&& c1 (> c1 (&& 0 (!= c0 0)))))
(min (+ (* (/ x c1) c1) c2) x) ==> b if (> c1 (&& 0 (>= c2 (- c1 1))))
(min x (+ (* (/ x c1) c1) c2)) ==> a if (> c1 (&& 0 (>= c2 (- c1 1))))
(min (* (/ (+ x c0) c1) c1) x) ==> b if (> c1 (&& 0 (>= c0 (- c1 1))))
(min x (* (/ (+ x c0) c1) c1)) ==> a if (> c1 (&& 0 (>= c0 (- c1 1))))
(min (+ (* (/ x c1) c1) c2) x) ==> a if (> c1 (&& 0 (<= c2 0)))
(min x (+ (* (/ x c1) c1) c2)) ==> b if (> c1 (&& 0 (<= c2 0)))
(min (* (/ (+ x c0) c1) c1) x) ==> a if (> c1 (&& 0 (<= c0 0)))
(min x (* (/ (+ x c0) c1) c1)) ==> b if (> c1 (&& 0 (<= c0 0)))
(min x (+ (max x y) c0)) ==> a if (<= 0 c0)
(min x (+ (max y x) c0)) ==> a if (<= 0 c0)
(min (+ (max x y) c0) x) ==> b if (<= 0 c0)
(min (+ (max x y) c0) y) ==> b if (<= 0 c0)
(min (max x (+ y c0)) y) ==> y if (> c0 0)
(min (max (- c0 x) x) c1) ==> b if (<= (* 2 c1) (+ c0 1))
(min (max x (- c0 x)) c1) ==> b if (<= (* 2 c1) (+ c0 1))
(min (min (/ x c0) y) (/ z c0)) ==> (min (/ (min x z) c0) y) if (> c0 0)
(min (max x c0) c1) ==> (max (min x c1) c0) if (<= c0 c1)
(min x (select (== x c0) c1 x)) ==> (select (== x c0) c1 x) if (< c1 c0)
(min x (select (== x c0) c1 x)) ==> x if (<= c0 c1)
(min (select (== x c0) c1 x) c2) ==> (min x c2) if (&& (<= c2 c0) (<= c2 c1))
(min (select (== x c0) c1 x) x) ==> (select (== x c0) c1 x) if (< c1 c0)
(min (select (== x c0) c1 x) x) ==> x if (<= c0 c1)
(min (+ (min x y) c0) x) ==> (min x (+ y c0)) if (> c0 0)
(min (+ (min x y) c0) x) ==> (+ (min x y) c0) if (< c0 0)
(min (+ (min y x) c0) x) ==> (min (+ y c0) x) if (> c0 0)
(min (+ (min y x) c0) x) ==> (+ (min y x) c0) if (< c0 0)
(min x (+ (min x y) c0)) ==> (min x (+ y c0)) if (> c0 0)
(min x (+ (min x y) c0)) ==> (+ (min x y) c0) if (< c0 0)
(min x (+ (min y x) c0)) ==> (min x (+ y c0)) if (> c0 0)
(min x (+ (min y x) c0)) ==> (+ (min x y) c0) if (< c0 0)
(min (min x y) (+ x c0)) ==> (min x y) if (> c0 0)
(min (min x y) (+ x c0)) ==> (min (+ x c0) y) if (< c0 0)
(min (min y x) (+ x c0)) ==> (min y x) if (> c0 0)
(min (min y x) (+ x c0)) ==> (min y (+ x c0)) if (< c0 0)
(min (max (+ x c0) y) x) ==> x if (> c0 0)
(min (* (+ (* x c0) y) c1) (+ (* x c2) z)) ==> (+ (min (* y c1) z) (* x c2)) if (== (* c0 c1) c2)
(min (* (+ y (* x c0)) c1) (+ (* x c2) z)) ==> (+ (min (* y c1) z) (* x c2)) if (== (* c0 c1) c2)
(min (* (+ (* x c0) y) c1) (+ z (* x c2))) ==> (+ (min (* y c1) z) (* x c2)) if (== (* c0 c1) c2)
(min (* (+ y (* x c0)) c1) (+ z (* x c2))) ==> (+ (min (* y c1) z) (* x c2)) if (== (* c0 c1) c2)
(min (/ x c0) (/ y c0)) ==> (/ (min x y) c0) if (> c0 0)
(min (/ x c0) (/ y c0)) ==> (/ (max x y) c0) if (< c0 0)
(min (* (/ (+ x c0) c1) c1) (+ x c2)) ==> (+ x c2) if (> c1 (&& 0 (>= (+ c0 1) (+ c1 c2))))
(min (* (min (/ (+ y c0) c1) x) c1) (+ y c2)) ==> (min (* x c1) (+ y c2)) if (> c1 (&& 0 (<= (+ c1 c2) (+ c0 1))))
(min (+ (* (min (/ (+ y c0) c1) x) c1) c2) y) ==> (min (+ (* x c1) c2) y) if (> c1 (&& 0 (<= c1 (+ (+ c0 c2) 1))))
(min (* (min (/ (+ y c0) c1) x) c1) y) ==> (min (* x c1) y) if (> c1 (&& 0 (<= c1 (+ c0 1))))
(min (/ (+ x c0) c1) (* (/ (+ x c2) c3) c4)) ==> (/ (+ x c0) c1) if (<= (- (+ c0 c3) c1) (&& c2 (> c1 (&& 0 (> c3 (&& 0 (== (* c1 c4) c3)))))))
(min (/ (+ x c0) c1) (* (/ (+ x c2) c3) c4)) ==> (* (/ (+ x c2) c3) c4) if (<= c2 (&& c0 (> c1 (&& 0 (> c3 (&& 0 (== (* c1 c4) c3)))))))
(min (/ x c1) (* (/ (+ x c2) c3) c4)) ==> (/ x c1) if (<= (- c3 c1) (&& c2 (> c1 (&& 0 (> c3 (&& 0 (== (* c1 c4) c3)))))))
(min (/ x c1) (* (/ (+ x c2) c3) c4)) ==> (* (/ (+ x c2) c3) c4) if (<= c2 (&& 0 (> c1 (&& 0 (> c3 (&& 0 (== (* c1 c4) c3)))))))
(min (/ (+ x c0) c1) (* (/ x c3) c4)) ==> (/ (+ x c0) c1) if (<= (- (+ c0 c3) c1) (&& 0 (> c1 (&& 0 (> c3 (&& 0 (== (* c1 c4) c3)))))))
(min (/ (+ x c0) c1) (* (/ x c3) c4)) ==> (* (/ x c3) c4) if (<= 0 (&& c0 (> c1 (&& 0 (> c3 (&& 0 (== (* c1 c4) c3)))))))
(min (/ x c1) (* (/ x c3) c4)) ==> (* (/ x c3) c4) if (> c1 (&& 0 (> c3 (&& 0 (== (* c1 c4) c3)))))
(- (min (+ x c0) y) (select z (+ (min x y) c1) x)) ==> (select z (- (max (min (- y x) c0) 0) c1) (min (- y x) c0)) if (> c0 0)
(- (min y (+ x c0)) (select z (+ (min y x) c1) x)) ==> (select z (- (max (min (- y x) c0) 0) c1) (min (- y x) c0)) if (> c0 0)
"#;

const CAVIAR_RULES: &str = r#"
(== ?x ?y) ==> (== ?y ?x)
(== ?x ?y) ==> (== (- ?x ?y) 0)
(== (+ ?x ?y) ?z) ==> (== ?x (- ?z ?y))
(== ?x ?x) ==> 1
(== (* ?x ?y) 0) ==> (|| (== ?x 0) (== ?y 0))
( == (max ?x ?y) ?y) ==> (<= ?x ?y)
( == (min ?x ?y) ?y) ==> (<= ?y ?x)
(<= ?y ?x) ==> ( == (min ?x ?y) ?y)
(== (* ?a ?x) ?b) ==> 0 if (&& (!= ?a 0) (!= (% ?b ?a) 0))
(== (max ?x ?c) 0) ==> 0 if (> ?c 0)
(== (max ?x ?c) 0) ==> (== ?x 0) if (< ?c 0)
(== (min ?x ?c) 0) ==> 0 if (< ?c 0)
(== (min ?x ?c) 0) ==> (== ?x 0) if (> ?c 0)
(|| ?x ?y) ==> (! (&& (! ?x) (! ?y)))
(|| ?y ?x) ==> (|| ?x ?y)
(+ ?a ?b) ==> (+ ?b ?a)
(+ ?a (+ ?b ?c)) ==> (+ (+ ?a ?b) ?c)
(+ ?a 0) ==> ?a
(* ?a (+ ?b ?c)) ==> (+ (* ?a ?b) (* ?a ?c))
(+ (* ?a ?b) (* ?a ?c)) ==> (* ?a (+ ?b ?c))
(+ (/ ?a ?b) ?c) ==> (/ (+ ?a (* ?b ?c)) ?b)
(/ (+ ?a (* ?b ?c)) ?b) ==> (+ (/ ?a ?b) ?c)
( + ( / ?x 2 ) ( % ?x 2 ) ) ==> ( / ( + ?x 1 ) 2 )
( + (* ?x ?a) (* ?y ?b)) ==> ( * (+ (* ?x (/ ?a ?b)) ?y) ?b) if (&& (!= ?b 0) (== (% ?a ?b) 0))
(/ 0 ?x) ==> (0)
(/ ?a ?a) ==> 1 if (!= ?a 0)
(/ (* -1 ?a) ?b) ==> (/ ?a (* -1 ?b))
(/ ?a (* -1 ?b)) ==> (/ (* -1 ?a) ?b)
(* -1 (/ ?a ?b)) ==> (/ (* -1 ?a) ?b)
(/ (* -1 ?a) ?b) ==> (* -1 (/ ?a ?b))
( / ( * ?x ?a ) ?b ) ==> ( / ?x ( / ?b ?a ) ) if (&& (> ?a 0) (== (% ?b ?a) 0))
( / ( * ?x ?a ) ?b ) ==> ( * ?x ( / ?a ?b ) ) if (&& (> ?b 0) (== (% ?a ?b) 0))
( / ( + ( * ?x ?a ) ?y ) ?b ) ==> ( + ( * ?x ( / ?a ?b ) ) ( / ?y ?b ) ) if (&& (> ?b 0) (== (% ?a ?b) 0))
( / ( + ?x ?a ) ?b ) ==> ( + ( / ?x ?b ) ( / ?a ?b ) ) if (&& (> ?b 0) (== (% ?a ?b) 0))
(!= ?x ?y) ==> (! (== ?x ?y))
(max ?a ?b) ==> (* -1 (min (* -1 ?a) (* -1 ?b)))
(&& ?y ?x) ==> (&& ?x ?y)
(&& ?a (&& ?b ?c)) ==> (&& (&& ?a ?b) ?c)
(&& 1 ?x) ==> ?x
(&& ?x ?x) ==> ?x
(&& ?x (! ?x)) ==> 0
( && ( == ?x ?c0 ) ( == ?x ?c1 ) ) ==> 0 if (!= ?c1 ?c0)
( && ( != ?x ?c0 ) ( == ?x ?c1 ) ) ==> ( == ?x ?c1 ) if (!= ?c1 ?c0)
(&& (< ?x ?y) (< ?x ?z)) ==> (< ?x (min ?y ?z))
(< ?x (min ?y ?z)) ==> (&& (< ?x ?y) (< ?x ?z))
(&& (<= ?x ?y) (<= ?x ?z)) ==> (<= ?x (min ?y ?z))
(<= ?x (min ?y ?z)) ==> (&& (<= ?x ?y) (<= ?x ?z))
(&& (< ?y ?x) (< ?z ?x)) ==> (< (max ?y ?z) ?x)
(> ?x (max ?y ?z)) ==> (&& (< ?z ?x) (< ?y ?x))
(&& (<= ?y ?x) (<= ?z ?x)) ==> (<= (max ?y ?z) ?x)
(>= ?x (max ?y ?z)) ==> (&& (<= ?z ?x) (<= ?y ?x))
( && ( < ?c0 ?x ) ( < ?x ?c1 ) ) ==> 0 if (<= ?c1 (+ ?c0 1))
( && ( <= ?c0 ?x ) ( <= ?x ?c1 ) ) ==> 0 if (< ?c1 ?c0)
( && ( <= ?c0 ?x ) ( < ?x ?c1 ) ) ==> 0 if (<= ?c1 ?c0)
(&& ?a (|| ?b ?c)) ==> (|| (&& ?a ?b) (&& ?a ?c))
(|| ?a (&& ?b ?c)) ==> (&& (|| ?a ?b) (|| ?a ?c))
(|| ?x (&& ?x ?y)) ==> ?x
(- ?a ?b) ==> (+ ?a (* -1 ?b))
(* ?a ?b) ==> (* ?b ?a)
(* ?a (* ?b ?c)) ==> (* (* ?a ?b) ?c)
(* ?a 0) ==> 0
(* ?a 1) ==> ?a
(* (/ ?a ?b) ?b) ==> (- ?a (% ?a ?b))
(* (max ?a ?b) (min ?a ?b)) ==> (* ?a ?b)
(/ (* ?y ?x) ?x) ==> ?y
(<= ?x ?y) ==> (! (< ?y ?x))
(! (< ?y ?x)) ==> (<= ?x ?y)
(>= ?x ?y) ==> (! (< ?x ?y))
(! (== ?x ?y)) ==> (!= ?x ?y)
(! (! ?x)) ==> ?x
(> ?x ?z) ==> (< ?z ?x)
(< ?x ?y) ==> (< (* -1 ?y) (* -1 ?x))
(< ?a ?a) ==> 0
(< (+ ?x ?y) ?z) ==> (< ?x (- ?z ?y))
(< ?z (+ ?x ?y)) ==> (< (- ?z ?y) ?x)
(< (- ?a ?y) ?a ) ==> 1 if (> ?y 0)
(< 0 ?y ) ==> 1 if (> ?y 0)
(< ?y 0 ) ==> 1 if (< ?y 0)
( < ( min ?x ?y ) ?x ) ==> ( < ?y ?x )
( < ( min ?z ?y ) ( min ?x ?y ) ) ==> ( < ?z ( min ?x ?y ) )
( < ( max ?z ?y ) ( max ?x ?y ) ) ==> ( < ( max ?z ?y ) ?x )
( < ( min ?z ?y ) ( min ?x ( + ?y ?c0 ) ) ) ==> ( < ( min ?z ?y ) ?x ) if (> ?c0 0)
( < ( max ?z ( + ?y ?c0 ) ) ( max ?x ?y ) ) ==> ( < ( max ?z ( + ?y ?c0 ) ) ?x ) if (> ?c0 0)
( < ( min ?z ( + ?y ?c0 ) ) ( min ?x ?y ) ) ==> ( < ( min ?z ( + ?y ?c0 ) ) ?x ) if (< ?c0 0)
( < ( max ?z ?y ) ( max ?x ( + ?y ?c0 ) ) ) ==> ( < ( max ?z ?y ) ?x ) if (< ?c0 0)
( < ( min ?x ?y ) (+ ?x ?c0) ) ==> 1 if (> ?c0 0)
(< (max ?a ?c) (min ?a ?b)) ==> 0
(< (* ?x ?y) ?z) ==> (< ?x ( / (- ( + ?z ?y ) 1 ) ?y ) )) if (> ?y 0)
(< ?y (/ ?x ?z)) ==> ( < ( - ( * ( + ?y 1 ) ?z ) 1 ) ?x ) if (> ?z 0)
(< ?a (% ?x ?b)) ==> 1 if (<= ?a (- 0 (abs ?b)))
(< ?a (% ?x ?b)) ==> 0 if (>= ?a (abs ?b))
(min ?a ?b) ==> (min ?b ?a)
(min (min ?x ?y) ?z) ==> (min ?x (min ?y ?z))
(min ?x ?x) ==> ?x
(min (max ?x ?y) ?x) ==> ?x
(min (max ?x ?y) (max ?x ?z)) ==> (max (min ?y ?z) ?x)
(min (max (min ?x ?y) ?z) ?y) ==> (min (max ?x ?z) ?y)
(min (+ ?a ?b) ?c) ==> (+ (min ?b (- ?c ?a)) ?a)
(+ (min ?x ?y) ?z) ==> (min (+ ?x ?z) (+ ?y ?z))
(min ?x (+ ?x ?a)) ==> ?x if (> ?a 0)
(min ?x (+ ?x ?a)) ==> (+ ?x ?a) if (< ?a 0)
(* (min ?x ?y) ?z) ==> (min (* ?x ?z) (* ?y ?z)) if (> ?z 0)
(min (* ?x ?z) (* ?y ?z)) ==> (* (min ?x ?y) ?z) if (> ?z 0)
(* (min ?x ?y) ?z) ==> (max (* ?x ?z) (* ?y ?z)) if (< ?z 0)
(max (* ?x ?z) (* ?y ?z)) ==> (* (min ?x ?y) ?z) if (< ?z 0)
(/ (min ?x ?y) ?z) ==> (min (/ ?x ?z) (/ ?y ?z)) if (> ?z 0)
(min (/ ?x ?z) (/ ?y ?z)) ==> (/ (min ?x ?y) ?z) if (> ?z 0)
(/ (max ?x ?y) ?z) ==> (min (/ ?x ?z) (/ ?y ?z)) if (< ?z 0)
(min (/ ?x ?z) (/ ?y ?z)) ==> (/ (max ?x ?y) ?z) if (< ?z 0)
( min ( max ?x ?c0 ) ?c1 ) ==> ?c1 if (<= ?c1 ?c0)
( min ( * ( / ?x ?c0 ) ?c0 ) ?x ) ==> ( * ( / ?x ?c0 ) ?c0 ) if (> ?c0 0)
(min (% ?x ?c0) ?c1) ==> (% ?x ?c0) if (>= ?c1 (- (abs ?c0) 1))
(min (% ?x ?c0) ?c1) ==> ?c1 if (<= ?c1 (- 0 (abs (+ ?c0 1))))
( min ( max ?x ?c0 ) ?c1 ) ==> ( max ( min ?x ?c1 ) ?c0 ) if (<= ?c0 ?c1)
( max ( min ?x ?c1 ) ?c0 ) ==> ( min ( max ?x ?c0 ) ?c1 ) if (<= ?c0 ?c1)
( < ( min ?y ?c0 ) ?c1 ) ==> ( || ( < ?y ?c1 ) ( < ?c0 ?c1 ) )
( < ( max ?y ?c0 ) ?c1 ) ==> ( && ( < ?y ?c1 ) ( < ?c0 ?c1 ) )
( < ?c1 ( max ?y ?c0 ) ) ==> ( || ( < ?c1 ?y ) ( < ?c1 ?c0 ) )
( min ( * ?x ?a ) ?b ) ==> ( * ( min ?x ( / ?b ?a ) ) ?a ) if (&& (> ?a 0) (== (% ?b ?a) 0))
( min ( * ?x ?a ) ( * ?y ?b ) ) ==> ( * ( min ?x ( * ?y ( / ?b ?a ) ) ) ?a ) if (&& (> ?a 0) (== (% ?b ?a) 0))
( min ( * ?x ?a ) ?b ) ==> ( * ( max ?x ( / ?b ?a ) ) ?a ) if (&& (< ?a 0) (== (% ?b ?a) 0))
( min ( * ?x ?a ) ( * ?y ?b ) ) ==> ( * ( max ?x ( * ?y ( / ?b ?a ) ) ) ?a ) if (&& (< ?a 0) (== (% ?b ?a) 0))
(% 0 ?x) ==> 0
(% ?x ?x) ==> 0
(% ?x 1) ==> 0
(% ?x ?c1) ==> (% (+ ?x ?c1) ?c1) if (<= ?c1 (abs ?x))
(% ?x ?c1) ==> (% (- ?x ?c1) ?c1) if (<= ?c1 (abs ?x))
(% (* ?x -1) ?c) ==> (* -1 (% ?x ?c))
(* -1 (% ?x ?c)) ==> (% (* ?x -1) ?c)
(% (- ?x ?y) 2) ==> (% (+ ?x ?y) 2)
( % ( + ( * ?x ?c0 ) ?y ) ?c1 ) ==> ( % ?y ?c1 ) if (&& (!= ?c1 0) (== (% ?c0 ?c1) 0))
(% (* ?c0 ?x) ?c1) ==> 0 if (&& (!= ?c1 0) (== (% ?c0 ?c1) 0))
"#;

fn run_derivability_tests<L: SynthLanguage>(
    base: &Ruleset<L>,
    against: &Ruleset<L>,
    implications: &ImplicationSet<L>,
) -> DerivabilityResult<L> {
    let impl_rules = implications.to_egg_rewrites();

    let (can, cannot) = base.derive(
        ruler::DeriveType::LhsAndRhs,
        against,
        Limits::deriving(),
        Some(&impl_rules),
    );

    DerivabilityResult { can, cannot }
}

fn halide_rules() -> Ruleset<Pred> {
    let rules = HALIDE_RULES;
    let mut ruleset = Ruleset::default();
    for line in rules.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let rule: Result<_, _> = Rule::from_string(line);
        if let Ok((rule, _)) = rule {
            if rule.is_valid() {
                ruleset.add(rule);
            } else {
                println!("Failed to validate rule: {}", line);
            }
        } else {
            println!("Failed to parse rule: {}", line);
        }
    }

    ruleset
}

fn caviar_rules() -> Ruleset<Pred> {
    let rules = CAVIAR_RULES;
    let mut ruleset = Ruleset::default();
    for rule in rules.trim().lines() {
        match Rule::from_string(rule) {
            Ok((rule, None)) => {
                if !rule.is_valid() {
                    println!("skipping {rule} because it is not valid");
                } else {
                    ruleset.add(rule);
                }
            }
            // This error can come from the inclusion of backwards rules:
            // the Caviar ruleset shouldn't have them.
            _ => panic!("Unable to parse single rule: {}", rule),
        }
    }
    ruleset
}

// The naive O(n^2) algorithm to build implications.
// Good for what we'll expect to see in the Caviar
// eval; bad for large sets of assumptions generated
// bottom-up.
fn pairwise_implication_building<L: SynthLanguage>(
    assumptions: &[Assumption<L>],
) -> ImplicationSet<L> {
    let mut implications = ImplicationSet::default();
    for a1 in assumptions {
        for a2 in assumptions {
            let name = format!("{a1} -> {a2}");
            let implication = Implication::new(name.into(), a1.clone(), a2.clone());
            if let Ok(implication) = implication {
                if !implications.contains(&implication) && implication.is_valid() {
                    implications.add(implication);
                }
            }
        }
    }
    implications
}

// Given a ruleset, can Chompy come up with each rule?
// Explodes if rules contains non-conditional rules.
// NOTE: this is not a #[test] because it doesn't work in CI.
#[allow(dead_code)]
fn can_synthesize_all<L: SynthLanguage>(rules: Ruleset<L>) -> (Ruleset<L>, Ruleset<L>) {
    let mut can = Ruleset::default();
    let mut cannot = Ruleset::default();
    for rule in rules.iter() {
        // we do this weird dummy rulest thing because
        // we need to make sure that the candidates that Chompy spits out
        // are equivalent to the rules in the ruleset under renaming.
        // that is, if the rule is `(f ?x) => (f ?y)`, we want to make
        // sure we're looking for `(f ?a) => (f ?b)`, because that's what
        // Chompy will spit out (if it finds it).
        let mut dummy_ruleset: Ruleset<L> = Ruleset::default();
        let lhs = L::instantiate(&rule.lhs);
        let rhs = L::instantiate(&rule.rhs);
        let cond = L::instantiate(&rule.cond.clone().unwrap().chop_assumption());

        dummy_ruleset.add_cond_from_recexprs(&lhs, &rhs, &cond, 0);

        // it might have accepted the backwards version of the rule, i guess.
        assert!(dummy_ruleset.len() <= 2);
        let desired_rule = dummy_ruleset.iter().take(1).next().unwrap();

        let workload = Workload::new(&[lhs.to_string(), rhs.to_string()]);

        // we append the term workload here because the condition workload
        // needs to have the same environment to evaluate cvecs under as the parent,
        // which means their set of variables must match.
        let cond_workload = Workload::new(&[cond.to_string()]).append(workload.clone());

        let predicate_map = build_pvec_to_patterns(cond_workload);

        let candidates = Ruleset::conditional_cvec_match(
            &workload.to_egraph(),
            &Ruleset::default(),
            &predicate_map,
            &ImplicationSet::default(),
        );

        println!("candidates: (tried to synthesize {rule})");
        for candidate in candidates.iter() {
            println!("  {candidate}");
        }

        let can_derive = match &desired_rule.cond {
            Some(_) => candidates.can_derive_cond(
                ruler::DeriveType::LhsAndRhs,
                desired_rule,
                Limits::deriving(),
                &vec![],
            ),
            None => candidates.can_derive(
                ruler::DeriveType::LhsAndRhs,
                desired_rule,
                Limits::deriving(),
            ),
        };

        if can_derive {
            can.add(rule.clone());
        } else {
            cannot.add(rule.clone());
        }
    }

    (can, cannot)
}

#[cfg(test)]
pub mod halide_derive_tests {
    use std::path::Path;

    use egg::{EGraph, RecExpr, Runner};
    use ruler::{
        conditions::{
            generate::{compress, get_condition_workload},
            implication_set::run_implication_workload,
        },
        enumo::{ChompyState, Filter, Metric},
        halide::og_recipe,
        recipe_utils::{
            base_lang, iter_metric, recursive_rules_cond, run_workload, run_workload_internal_llm,
            Lang,
        },
        time_fn_call, DeriveType, SynthAnalysis,
    };

    use super::*;

    #[test]
    fn mul_div_workload() {
        if std::env::var("RUN_ME").is_err() {
            return;
        }

        let wkld = get_condition_workload();

        let cond_workload = Workload::new(&[
            "(&& (< 0 a) (== (% b a) 0))",
            "(&& (< 0 a) (== (% b a) 0))",
            "(&& (< a 0) (== (% b a) 0))",
            "(&& (< a 0) (== (% b a) 0))",
            "(!= a 0)",
            "(!= b 0)",
            "(!= c 0)",
            "(== c c)",
        ]);

        let mut base_implications = ImplicationSet::default();

        // and the "and" rules here.
        let and_implies_left: Implication<Pred> = Implication::new(
            "and_implies_left".into(),
            Assumption::new("(&& ?a ?b)".to_string()).unwrap(),
            Assumption::new_unsafe("?a".to_string()).unwrap(),
        )
        .unwrap();

        let and_implies_right: Implication<Pred> = Implication::new(
            "and_implies_right".into(),
            Assumption::new("(&& ?a ?b)".to_string()).unwrap(),
            Assumption::new_unsafe("?b".to_string()).unwrap(),
        )
        .unwrap();

        base_implications.add(and_implies_left);
        base_implications.add(and_implies_right);

        let other_implications = time_fn_call!(
            "find_base_implications",
            run_implication_workload(
                &wkld,
                &["a".to_string(), "b".to_string(), "c".to_string()],
                &base_implications,
                &Default::default()
            )
        );

        base_implications.add_all(other_implications);

        println!("# base implications: {}", base_implications.len());

        for i in base_implications.iter() {
            println!("implication: {}", i.name());
        }

        let mut all_rules: Ruleset<Pred> = Ruleset::default();

        all_rules.add(Rule::from_string("(!= ?a ?b) ==> (!= ?b ?a)").unwrap().0);

        let rules = recursive_rules_cond(
            Metric::Atoms,
            3,
            Lang::new(
                &["0", "1"],
                &["a", "b", "c"],
                &[&[], &["*", "/", "min", "max"]],
            ),
            all_rules.clone(),
            base_implications.clone(),
            cond_workload,
            false,
        );

        all_rules.extend(rules);

        for line in r#"
(/ (* ?x ?a) ?b) ==> (/ ?x (/ ?b ?a)) if (&& (> ?a 0) (== (% ?b ?a) 0))
(/ (* ?x ?a) ?b) ==> (* ?x (/ ?a ?b)) if (&& (> ?b 0) (== (% ?a ?b) 0))
(min (* ?x ?a) ?b) ==> (* (min ?x (/ ?b ?a)) ?a) if (&& (> ?a 0) (== (% ?b ?a) 0))
(min (* ?x ?a) (* ?y ?b)) ==> (* (min ?x (* ?y (/ ?b ?a))) ?a) if (&& (> ?a 0) (== (% ?b ?a) 0))
(min (* ?x ?a) ?b) ==> (* (max ?x (/ ?b ?a)) ?a) if (&& (< ?a 0) (== (% ?b ?a) 0))
(min (* ?x ?a) (* ?y ?b)) ==> (* (max ?x (* ?y (/ ?b ?a))) ?a) if (&& (< ?a 0) (== (% ?b ?a) 0))
"#
        .lines()
        {
            if line.trim().is_empty() {
                continue;
            }
            let rule = Rule::from_string(line.trim())
                .expect("Failed to parse rule")
                .0;
            assert!(rule.is_valid());
            if !all_rules.can_derive_cond(
                ruler::DeriveType::LhsAndRhs,
                &rule,
                Limits::deriving(),
                &base_implications.to_egg_rewrites(),
            ) {
                println!("Hey.. we weren't able to derive this rule: {rule}");
                continue;
            }

            let l_expr = Pred::instantiate(&rule.lhs);
            let r_expr = Pred::instantiate(&rule.rhs);
            let c_expr = Pred::instantiate(&rule.cond.clone().unwrap().chop_assumption());

            let mut egraph: EGraph<Pred, SynthAnalysis> =
                EGraph::default().with_explanations_enabled();
            egraph.add_expr(&l_expr);
            egraph.add_expr(&r_expr);

            let c_assumption = Assumption::new(c_expr.to_string()).unwrap();
            c_assumption.insert_into_egraph(&mut egraph);

            // 0. run the implications.
            let runner: Runner<Pred, SynthAnalysis> = Runner::default()
                .with_explanations_enabled()
                .with_egraph(egraph.clone())
                .run(base_implications.to_egg_rewrites().iter());

            let egraph = runner.egraph;

            // 1. run the rules.
            let mut runner: Runner<Pred, SynthAnalysis> = Runner::default()
                .with_explanations_enabled()
                .with_egraph(egraph)
                .run(all_rules.iter().map(|r| &r.rewrite));

            let mut proof = runner.explain_equivalence(&l_expr, &r_expr);

            println!("Here is the proof for why the rule is derivable:");
            println!("{}", proof.get_flat_string());
        }
    }

    // TODO: fix mii
    const USE_LLM: bool = false;

    #[tokio::test]
    async fn op_min_max_workload_with_llm() {
        let start_time = std::time::Instant::now();
        if std::env::var("RUN_ME").is_err() {
            println!("Not running op_min_max_workload_with_llm test because RUN_ME is not set.");
            return;
        }

        // this workload will consist of well-typed lt comparisons, where the child
        // expressions consist of variables, `+`, and `min` (of up to size 5).
        let int_workload = iter_metric(base_lang(2), "EXPR", Metric::Atoms, 5)
            .filter(Filter::And(vec![
                Filter::Excludes("VAL".parse().unwrap()),
                Filter::Excludes("OP1".parse().unwrap()),
            ]))
            .plug("OP2", &Workload::new(&["min", "+"]))
            .plug("VAR", &Workload::new(&["a", "b", "c", "d"]));

        let lt_workload = Workload::new(&["(OP V V)"])
            .plug("OP", &Workload::new(&["<"]))
            .plug("V", &int_workload)
            .filter(Filter::Canon(vec![
                "a".to_string(),
                "b".to_string(),
                "c".to_string(),
                "d".to_string(),
            ]));

        let cond_workload = Workload::new(&["(OP2 V 0)"])
            .plug("OP2", &Workload::new(&["<"]))
            .plug(
                "V",
                &Workload::new(&["(< a 0)", "(== b b)", "(== c c)", "(== d d)"]),
            );

        // These are rules which will help compress the workload so we can mimic
        // focus on "realistic" candidate spaces for large grammars.
        let mut prior: Ruleset<Pred> = Ruleset::default();

        let prior_str = r#"(min ?a ?a) <=> ?a
(max ?a ?a) <=> (min ?a ?a)
(min ?b ?a) <=> (min ?a ?b)
(max ?b ?a) <=> (max ?a ?b)
(min ?b ?a) ==> ?a if (< ?a ?b)
(max ?b ?a) ==> ?b if (< ?a ?b)
(min ?b (max ?b ?a)) ==> ?b
(max ?a (min ?b ?a)) ==> ?a
(min ?c (min ?b ?a)) <=> (min ?a (min ?b ?c))
(min ?b (min ?b ?a)) <=> (min ?a (min ?b ?a))
(min ?a (max ?b ?a)) <=> (max ?a (min ?b ?a))
(max ?c (max ?b ?a)) <=> (max ?b (max ?c ?a))
(max ?c (min ?b ?a)) ==> (min ?a (max ?c ?b)) if  (< ?c ?a)
(max (min ?a ?c) (min ?b ?c)) <=> (min ?c (max ?b ?a))
(max ?b (min ?c (max ?b ?a))) <=> (max ?b (min ?a ?c))
(min ?a (max ?c (min ?b ?a))) <=> (max (min ?c ?a) (min ?b ?a))
(min (max ?b ?c) (max ?b ?a)) <=> (max ?b (min ?a (max ?b ?c)))
(max ?b (min ?c (max ?b ?a))) <=> (max ?b (min ?a (max ?b ?c)))
(+ ?a 0) <=> ?a
(+ ?a ?b) <=> (+ ?b ?a)
(< ?a ?b) ==> 1 if (< ?a ?b)
(< ?a ?b) ==> 0 if (< ?b ?a)"#;

        for line in prior_str.lines() {
            let rule: Rule<Pred> = Rule::from_string(line).unwrap().0;
            assert!(rule.is_valid(), "Rule is not valid: {}", rule);
            prior.add(rule);
        }

        let mut state: ChompyState<Pred> = ChompyState::new(
            lt_workload.clone(),
            prior.clone(),
            cond_workload.clone(),
            // we don't need any implications for this test; notice how
            // all the conditions are just `(< ?a ?b)`.
            ImplicationSet::default(),
        );

        let rules = run_workload_internal_llm(
            &mut state,
            Limits::synthesis(),
            Limits::minimize(),
            true,
            true,
            true,
        )
        .await;

        // (< (min ?z (+ ?y ?c0)) (min ?x ?y)) ==> (< (min ?z (+ ?y ?c0)) ?x) if (< ?c0 0)
        let mut egraph: EGraph<Pred, SynthAnalysis> = EGraph::default().with_explanations_enabled();
        let l_expr: RecExpr<Pred> = "(< (min z (+ y c0)) (min x y))".parse().unwrap();
        let r_expr: RecExpr<Pred> = "(< (min z (+ y c0)) x)".parse().unwrap();
        let l_id = egraph.add_expr(&l_expr);
        let r_id = egraph.add_expr(&r_expr);
        egraph.add_expr(&"(assume (< c0 0))".parse().unwrap());

        let runner: Runner<Pred, SynthAnalysis> = egg::Runner::new(SynthAnalysis::default())
            .with_egraph(egraph.clone())
            .with_explanations_enabled()
            .with_node_limit(100000)
            .run(rules.iter().map(|r| &r.rewrite));

        let mut out_egraph = runner.egraph;

        let end_time = std::time::Instant::now();
        println!("Time taken: {:?}", end_time - start_time);

        if out_egraph.find(l_id) == out_egraph.find(r_id) {
            println!("The rule was derived: (< (min z (+ y c0)) (min x y)) ==> (< (min z (+ y c0)) x) if (< c0 0)");
            println!("Here's the proof:");
            let proof = out_egraph.explain_equivalence(&l_expr, &r_expr);
            println!("\n{proof}");
        } else {
            println!("The rule was NOT derived.");
        }
    }

    /// This takes a long time if we don't adjust the Limits and the Scheduler.
    #[test]
    fn op_min_max_workload() {
        let start_time = std::time::Instant::now();
        if std::env::var("RUN_ME").is_err() {
            return;
        }

        // this workload will consist of well-typed lt comparisons, where the child
        // expressions consist of variables, `+`, and `min` (of up to size 5).
        let int_workload = iter_metric(base_lang(2), "EXPR", Metric::Atoms, 5)
            .filter(Filter::And(vec![
                Filter::Excludes("VAL".parse().unwrap()),
                Filter::Excludes("OP1".parse().unwrap()),
            ]))
            .plug("OP2", &Workload::new(&["min", "+"]))
            .plug("VAR", &Workload::new(&["a", "b", "c", "d"]));

        let lt_workload = Workload::new(&["(OP V V)", "0", "1"])
            .plug("OP", &Workload::new(&["<"]))
            .plug("V", &int_workload)
            .filter(Filter::Canon(vec![
                "a".to_string(),
                "b".to_string(),
                "c".to_string(),
                "d".to_string(),
            ]));

        let cond_workload = Workload::new(&["(OP2 V 0)"])
            .plug("OP2", &Workload::new(&["<"]))
            .plug(
                "V",
                &Workload::new(&["(< a 0)", "(< b 0)", "(< 0 c)", "(< d 0)", "(< 0 d)"]),
            );

        // These are rules which will help compress the workload so we can mimic
        // focus on "realistic" candidate spaces for large grammars.
        let mut prior: Ruleset<Pred> = Ruleset::default();

        let prior_str = r#"(min ?a ?a) <=> ?a
(max ?a ?a) <=> (min ?a ?a)
(min ?b ?a) <=> (min ?a ?b)
(max ?b ?a) <=> (max ?a ?b)
(min ?b ?a) ==> ?a if (< ?a ?b)
(max ?b ?a) ==> ?b if (< ?a ?b)
(min ?b (max ?b ?a)) ==> ?b
(max ?a (min ?b ?a)) ==> ?a
(min ?c (min ?b ?a)) <=> (min ?a (min ?b ?c))
(min ?b (min ?b ?a)) <=> (min ?a (min ?b ?a))
(min ?a (max ?b ?a)) <=> (max ?a (min ?b ?a))
(max ?c (max ?b ?a)) <=> (max ?b (max ?c ?a))
(max ?c (min ?b ?a)) ==> (min ?a (max ?c ?b)) if  (< ?c ?a)
(max (min ?a ?c) (min ?b ?c)) <=> (min ?c (max ?b ?a))
(max ?b (min ?c (max ?b ?a))) <=> (max ?b (min ?a ?c))
(min ?a (max ?c (min ?b ?a))) <=> (max (min ?c ?a) (min ?b ?a))
(min (max ?b ?c) (max ?b ?a)) <=> (max ?b (min ?a (max ?b ?c)))
(max ?b (min ?c (max ?b ?a))) <=> (max ?b (min ?a (max ?b ?c)))
(+ ?a 0) <=> ?a
(+ ?a ?b) <=> (+ ?b ?a)
(< ?a ?b) ==> 1 if (< ?a ?b)
(< ?a ?b) ==> 0 if (< ?b ?a)"#;

        for line in prior_str.lines() {
            let rule: Rule<Pred> = Rule::from_string(line).unwrap().0;
            assert!(rule.is_valid(), "Rule is not valid: {}", rule);
            prior.add(rule);
        }

        let mut should_derive: Ruleset<Pred> = Default::default();
        should_derive.add(
            Rule::from_string(
                "(< (min ?z (+ ?y ?c0)) (min ?x ?y)) ==> (< (min ?z (+ ?y ?c0)) ?x) if (< ?c0 0)",
            )
            .unwrap()
            .0,
        );

        // I rewrote the condition. On the sheet, it's `(> ?c0 0)`, but this workload doesn't
        // know what greater than is.
        // In the real Chompy runs, the condition above should get rewritten as
        // `(< ?c0 0)`, in which case the same rules above should be able to
        // derive the rule.
        should_derive.add(
            Rule::from_string("(< (min ?x ?y) (+ ?x ?c0)) ==> 1 if (< 0 ?c0)")
                .unwrap()
                .0,
        );

        should_derive.add(
            Rule::from_string(
                "(< (min ?a ?b) (min ?c (+ ?b ?d))) ==> (< (min ?a ?b) ?c) if (< 0 ?d)",
            )
            .unwrap()
            .0,
        );

        for rule in should_derive.iter() {
            assert!(rule.is_valid(), "Rule is not valid: {}", rule);
        }

        let rules = run_workload(
            lt_workload.clone(),
            Some(cond_workload.clone()),
            prior.clone(),
            // we don't need any implications for this test; notice how
            // all the conditions are just `(< ?a ?b)`.
            ImplicationSet::default(),
            Limits::synthesis(),
            Limits::minimize(),
            true,
            false,
        );

        // NOTE : doing this manual derivation scheme for now because I don't have total
        //        faith that the unsound merge problem has gone away; I want to
        //        look at the proofs.
        for rule in should_derive.iter() {
            let mut egraph: EGraph<Pred, SynthAnalysis> =
                EGraph::default().with_explanations_enabled();
            let l_expr = Pred::instantiate(&rule.lhs);
            let r_expr = Pred::instantiate(&rule.rhs);
            let cond_expr = Pred::instantiate(&rule.cond.clone().unwrap().chop_assumption());
            let l_id = egraph.add_expr(&l_expr);
            let r_id = egraph.add_expr(&r_expr);
            egraph.add_expr(
                &format!("({} {})", Pred::assumption_label(), cond_expr)
                    .parse()
                    .unwrap(),
            );

            let runner: Runner<Pred, SynthAnalysis> = egg::Runner::new(SynthAnalysis::default())
                .with_egraph(egraph.clone())
                .with_explanations_enabled()
                .with_node_limit(100000)
                .run(rules.iter().map(|r| &r.rewrite));

            let mut out_egraph = runner.egraph;

            let end_time = std::time::Instant::now();
            println!("Time taken: {:?}", end_time - start_time);

            if out_egraph.find(l_id) == out_egraph.find(r_id) {
                println!("Derived the rule!");
                println!("Here's the proof:");
                let proof = out_egraph.explain_equivalence(&l_expr, &r_expr);
                println!("\n{proof}");
            } else {
                panic!("The rule was NOT derived.");
            }
        }
    }

    #[test]
    fn chompy_vs_halide() {
        if std::env::var("SKIP_RECIPES").is_ok() {
            return;
        }

        let binding = std::env::var("OUT_DIR").expect("OUT_DIR environment variable not set")
            + "/halide-derive.json";

        let halide_rules = halide_rules();

        println!("Parsed {} Halide rules", halide_rules.len());
    }

    #[test]
    // A simple derivability test.
    // How many conditional Caviar rules can Chompy's rulesets derive?
    // Vice versa: how many of Chompy's rules can Caviar derive?
    fn chompy_vs_caviar_conditional_derive() {
        // Don't run this test as part of the "unit tests" thing in CI.
        if std::env::var("SKIP_RECIPES").is_ok() {
            return;
        }

        // root directory: "out/derive.json"
        let binding = std::env::var("OUT_DIR").expect("OUT_DIR environment variable not set")
            + "/derive.json";
        let out_path: &Path = Path::new(&binding);
        let chompy_rules = og_recipe();
        let caviar_rules = caviar_rules();

        let all_conditions: Vec<_> = caviar_rules
            .iter()
            .chain(chompy_rules.iter())
            .filter_map(|r| {
                r.cond.as_ref().and_then(|c| {
                    Assumption::new(
                        Pred::generalize(
                            &Pred::instantiate(&c.chop_assumption()),
                            &mut Default::default(),
                        )
                        .to_string(),
                    )
                    .ok()
                })
            })
            .collect();

        let mut all_conditions = all_conditions.clone();
        all_conditions.sort_by(|a, b| a.to_string().cmp(&b.to_string()));
        all_conditions.dedup();

        let mut implication_rules: ImplicationSet<Pred> =
            pairwise_implication_building(&all_conditions);

        let and_implies_left: Implication<Pred> = Implication::new(
            "and_implies_left".into(),
            Assumption::new("(&& ?a ?b)".to_string()).unwrap(),
            Assumption::new_unsafe("?a".to_string()).unwrap(),
        )
        .unwrap();

        let and_implies_right: Implication<Pred> = Implication::new(
            "and_implies_right".into(),
            Assumption::new("(&& ?a ?b)".to_string()).unwrap(),
            Assumption::new_unsafe("?b".to_string()).unwrap(),
        )
        .unwrap();

        implication_rules.add(and_implies_left);
        implication_rules.add(and_implies_right);

        let keep_conditional = |rs: &Ruleset<Pred>| -> Ruleset<Pred> {
            let (conditional, _) = rs.partition(|r| r.cond.is_some());
            conditional
        };

        let forward_result = run_derivability_tests(
            &chompy_rules,
            &keep_conditional(&caviar_rules),
            &implication_rules,
        );
        let backward_result =
            run_derivability_tests(&caviar_rules, &keep_conditional(&chompy_rules), &implication_rules);

        let to_json = |result: DerivabilityResult<Pred>| {
            serde_json::json!({
                "can": result.can.iter().map(|r| r.to_string()).collect::<Vec<_>>(),
                "cannot": result.cannot.iter().map(|r| r.to_string()).collect::<Vec<_>>(),
            })
        };

        let to_write = serde_json::json!({
            "forwards": to_json(forward_result),
            "backwards": to_json(backward_result),
        });
        std::fs::write(out_path, to_write.to_string())
            .expect("Failed to write derivability results to file");
    }

    // A test to see if we can correctly choose all Caviar handwritten rules
    // as candidates.
    // Commenting this out, because it fails in CI.
    #[test]
    fn synthesize_all_caviar_as_candidates() {
        // Don't run this test as part of the "unit tests" thing in CI.
        if std::env::var("SKIP_RECIPES").is_ok() {
            return;
        }
        let caviar_rules = caviar_rules();

        let mut cond_num = 0;
        for r in caviar_rules.iter() {
            if r.cond.is_some() {
                cond_num += 1;
                println!("caviar rule: {r}");
            }
        }

        println!(
            "in total, {} conditional rules (out of {})",
            cond_num,
            caviar_rules.len()
        );

        // let caviar_conditional_rules = caviar_rules().partition(|r| r.cond.is_some()).0;
        // let (_, cannot) = can_synthesize_all(caviar_conditional_rules.clone());
        // assert!(
        //     cannot.is_empty(),
        //     "Chompy couldn't synthesize these rules: {:?}",
        //     cannot
        // );
    }

    #[test]
    // This test makes sure that Chompy's derivability (minimization)
    // algorithm is robust enough to not synthesize both of these rules
    // (it needs to just pick one):
    // // (min ?a ?b) ==> ?a if (<= ?a ?b)
    // // (min ?a ?b) ==> ?b if (<= ?b ?a)
    // // (min ?b ?a) ==> ?b if (<= ?b ?a)
    // // (min ?b ?a) ==> ?a if (<= ?a ?b)
    fn chompy_shouldnt_make_these() {
        if std::env::var("SKIP_RECIPES").is_ok() {
            return;
        }

        let cond_workload = Workload::new(&["(OP V V)"])
            .plug("OP", &Workload::new(&["<", "<="]))
            .plug("V", &Workload::new(&["a", "b", "c", "0", "1"]));

        let rules = run_workload(
            cond_workload.clone(),
            None,
            Ruleset::default(),
            ImplicationSet::default(),
            Limits::synthesis(),
            Limits::minimize(),
            true,
            USE_LLM,
        );

        let cond_workload = compress(&cond_workload, rules.clone());

        let implications = run_implication_workload(
            &cond_workload,
            &["a".to_string(), "b".to_string(), "c".to_string()],
            &Default::default(),
            &rules,
        );

        let min_max_rules: Ruleset<Pred> = recursive_rules_cond(
            Metric::Atoms,
            3,
            Lang::new(&[], &["a", "b", "c"], &[&[], &["min", "max"]]),
            rules.clone(),
            implications.clone(),
            cond_workload.clone(),
            USE_LLM,
        );

        println!("min_max_rules: {}", min_max_rules.len());
        for r in min_max_rules.iter() {
            println!("  {r}");
        }

        let mut against: Ruleset<Pred> = Ruleset::default();
        against.add(
            Rule::from_string("(min ?a ?b) ==> ?a if (<= ?a ?b)")
                .unwrap()
                .0,
        );

        against.add(
            Rule::from_string("(min ?a ?b) ==> ?b if (<= ?b ?a)")
                .unwrap()
                .0,
        );

        against.add(
            Rule::from_string("(min ?b ?a) ==> ?b if (<= ?b ?a)")
                .unwrap()
                .0,
        );

        against.add(
            Rule::from_string("(min ?b ?a) ==> ?a if (<= ?a ?b)")
                .unwrap()
                .0,
        );

        min_max_rules.pretty_print();

        let mut matches = 0;
        for r in against.iter() {
            assert!(min_max_rules.can_derive_cond(
                ruler::DeriveType::LhsAndRhs,
                r,
                Limits::deriving(),
                &implications.to_egg_rewrites(),
            ));
            if min_max_rules.contains(r) {
                matches += 1;
            }
        }

        assert_eq!(matches, 1);
    }

    // A sanity test.
    // If we can't synthesize these rules, or synthesize rules that derive
    // them, something terrible has happened.
    #[test]
    fn chompy_cant_forget_these() {
        if std::env::var("SKIP_RECIPES").is_ok() {
            return;
        }
        let mut all_rules: Ruleset<Pred> = Ruleset::default();
        let mut expected: Ruleset<Pred> = Default::default();
        for line in r#"(* (min ?x ?y) ?z) ==> (min (* ?x ?z) (* ?y ?z)) if (> ?z 0)
(min (* ?x ?z) (* ?y ?z)) ==> (* (min ?x ?y) ?z) if (> ?z 0)
(* (min ?x ?y) ?z) ==> (max (* ?x ?z) (* ?y ?z)) if (< ?z 0)
(max (* ?x ?z) (* ?y ?z)) ==> (* (min ?x ?y) ?z) if (< ?z 0)
(min ?a ?b) ==> ?a if (<= ?a ?b)
(max ?a ?b) ==> ?a if (<= ?b ?a)
(min ?a (+ ?a ?b)) ==> ?a if (<= 0 ?b)
(min ?a (+ ?a ?b)) ==> (+ ?a ?b) if (<= ?b 0)
(max ?a (+ ?a ?b)) ==> ?a if (<= ?b 0)
(max ?a (+ ?a ?b)) ==> (+ ?a ?b) if (<= 0 ?b)"#
            .lines()
        {
            let rule: Rule<Pred> = Rule::from_string(line).unwrap().0;
            assert!(rule.is_valid());
            expected.add(rule);
        }

        let cond_wkld = &Workload::new(&["(OP2 V V)"])
            .plug("OP2", &Workload::new(&["<", "<=", ">", ">="]))
            .plug("V", &Workload::new(&["a", "b", "c", "0"]));

        let cond_rules: Ruleset<Pred> = run_workload(
            cond_wkld.clone(),
            None,
            Ruleset::default(),
            ImplicationSet::default(),
            Limits::synthesis(),
            Limits::minimize(),
            true,
            USE_LLM,
        );

        all_rules.extend(cond_rules.clone());

        let cond_wkld = compress(cond_wkld, cond_rules.clone());

        println!("compressed");
        for c in cond_wkld.clone().force() {
            println!("c: {c}");
        }

        let implications = run_implication_workload(
            &cond_wkld,
            &["a".to_string(), "b".to_string(), "c".to_string()],
            &Default::default(),
            &cond_rules,
        );

        for i in implications.iter() {
            println!("i: {}", i.name());
        }

        let min_max_add_rules = recursive_rules_cond(
            Metric::Atoms,
            5,
            Lang::new(&[], &["a", "b", "c"], &[&[], &["min", "max", "+"]]),
            all_rules.clone(),
            implications.clone(),
            cond_wkld.clone(),
            USE_LLM,
        );

        all_rules.extend(min_max_add_rules);

        let min_max_sub_rules = recursive_rules_cond(
            Metric::Atoms,
            5,
            Lang::new(&[], &["a", "b", "c"], &[&[], &["min", "max", "-"]]),
            all_rules.clone(),
            implications.clone(),
            cond_wkld.clone(),
            USE_LLM,
        );

        all_rules.extend(min_max_sub_rules);

        let min_max_mul_rules = recursive_rules_cond(
            Metric::Atoms,
            7,
            Lang::new(&[], &["a", "b", "c"], &[&[], &["min", "max", "*"]]),
            all_rules.clone(),
            implications.clone(),
            cond_wkld.clone(),
            USE_LLM,
        );

        all_rules.extend(min_max_mul_rules);

        for r in expected.iter() {
            assert!(
                all_rules.can_derive_cond(
                    ruler::DeriveType::LhsAndRhs,
                    r,
                    Limits::deriving(),
                    &implications.to_egg_rewrites(),
                ),
                "couldn't derive rule: {}",
                r
            );
        }
    }

    // #[test]
    // fn test_timeout() {
    //     let mut chompy_rules: Ruleset<Pred> = Ruleset::from_file("/Users/acheung/research/projects/chompy/with-timeout.txt");
    //     // for line in CHOMPY_RULES.lines() {
    //     //     let line = line.trim();
    //     //     if line.is_empty() {
    //     //         continue;
    //     //     }

    //     //     let res = Rule::from_string(line);

    //     //     if res.is_err() {
    //     //         panic!("Failed to parse rule: {}", line);
    //     //     }

    //     //     let (fw, bw) = res.unwrap();

    //     //     rules.add(fw);

    //     //     if let Some(bw) = bw {
    //     //         rules.add(bw);
    //     //     }
    //     // }

    //     println!("our rules:");
    //     for r in chompy_rules.iter() {
    //         println!("  {r}");
    //     }

    //     let caviar_rules = caviar_rules();

    //     let mut can: Ruleset<Pred> = Ruleset::default();
    //     let mut cannot: Ruleset<Pred> = Ruleset::default();

    //     let mut all_conditions: Vec<_> = caviar_rules
    //         .iter()
    //         .chain(chompy_rules.iter())
    //         .filter_map(|r| {
    //             r.cond.as_ref().and_then(|c| {
    //                 Assumption::new(
    //                     Pred::generalize(
    //                         &Pred::instantiate(&c.chop_assumption()),
    //                         &mut Default::default(),
    //                     )
    //                     .to_string(),
    //                 )
    //                 .ok()
    //             })
    //         })
    //         .collect();

    //     println!("initial length: {}", all_conditions.len());

    //     all_conditions.sort_by(|a, b| a.to_string().cmp(&b.to_string()));
    //     all_conditions.dedup();

    //     println!("final length: {}", all_conditions.len());

    //     println!("all_conditions:");
    //     for c in all_conditions.iter() {
    //         println!("  {}", c);
    //     }

    //     let implication_rules: ImplicationSet<Pred> =
    //         pairwise_implication_building(&all_conditions);

    //     for c in caviar_rules.iter() {
    //         if c.cond.is_some() {
    //             println!("I'm trying to derive: {c}");
    //             let derive_result = time_fn_call!(
    //                 format!("can_derive_{}", c.name),
    //                 chompy_rules.can_derive_cond(DeriveType::LhsAndRhs, c, Limits::deriving(), &implication_rules.to_egg_rewrites()));
    //             if derive_result {
    //                 can.add(c.clone());
    //             } else {
    //                 cannot.add(c.clone());
    //             }
    //         }
    //     }

    //     let result = DerivabilityResult { can, cannot };

    //     // write it to derive-with-timeout.json
    //     let binding = std::env::var("OUT_DIR").expect("OUT_DIR environment variable not set")
    //         + "/derive-with-timeout.json";

    //     let out_path: &Path = Path::new(&binding);

    //     println!("I derived {}", result.can.len());
    //     println!("I could not derive {}", result.cannot.len());

    //     let result_json = |result: DerivabilityResult<Pred>| {
    //         serde_json::json!({
    //             "can": result.can.iter().map(|r| r.to_string()).collect::<Vec<_>>(),
    //             "cannot": result.cannot.iter().map(|r| r.to_string()).collect::<Vec<_>>(),
    //         })
    //     };

    //     std::fs::write(out_path, result_json(result).to_string())
    //         .expect("Failed to write derivability results to file");

    // }
}
