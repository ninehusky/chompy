use std::path::Path;

use ruler::{
    conditions::{
        assumption::Assumption, implication::Implication, implication_set::ImplicationSet,
    },
    enumo::{build_pvec_to_patterns, Rule, Ruleset, Workload},
    halide::{og_recipe, Pred},
    Limits, SynthLanguage,
};

struct DerivabilityResult<L: SynthLanguage> {
    can: Ruleset<L>,
    cannot: Ruleset<L>,
}

const HALIDE_TOTAL_RULES: &str = r#"(! (< x y)) ==> (<= y x)
(! (<= x y)) ==> (< y x)
(! (== x y)) ==> (!= x y)
(! (!= x y)) ==> (== x y)
(! (! x)) ==> x
(! (likely x)) ==> (likely (! x))
(! (likely_if_innermost x)) ==> (likely_if_innermost (! x))
(! (&& (! x) y)) ==> (|| x (! y))
(! (|| (! x) y)) ==> (&& x (! y))
(! (&& x (! y))) ==> (|| (! x) y)
(! (|| x (! y))) ==> (&& (! x) y)
(< x x) ==> 0
(< (max x y) x) ==> 0
(< (max y x) x) ==> 0
(< x (min x y)) ==> 0
(< x (min y x)) ==> 0
(< (max y z) (min x y)) ==> 0
(< (max y z) (min y x)) ==> 0
(< (max z y) (min x y)) ==> 0
(< (max z y) (min y x)) ==> 0
(< (- x y) z) ==> (< x (+ z y))
(< z (- x y)) ==> (< (+ z y) x)
(< (+ (- x y) z) w) ==> (< (+ x z) (+ y w))
(< (+ z (- x y)) w) ==> (< (+ x z) (+ y w))
(< w (+ (- x y) z)) ==> (< (+ w y) (+ x z))
(< w (+ z (- x y))) ==> (< (+ w y) (+ x z))
(< (+ (+ (- x y) z) u) w) ==> (< (+ (+ x z) u) (+ w y))
(< (+ (+ z (- x y)) u) w) ==> (< (+ (+ x z) u) (+ w y))
(< (+ u (+ (- x y) z)) w) ==> (< (+ (+ x z) u) (+ w y))
(< (+ u (+ z (- x y))) w) ==> (< (+ (+ x z) u) (+ w y))
(< w (+ (+ (- x y) z) u)) ==> (< (+ w y) (+ (+ x z) u))
(< w (+ (+ z (- x y)) u)) ==> (< (+ w y) (+ (+ x z) u))
(< w (+ u (+ (- x y) z))) ==> (< (+ w y) (+ (+ x z) u))
(< w (+ u (+ z (- x y)))) ==> (< (+ w y) (+ (+ x z) u))
(< x (+ x y)) ==> (< 0 y)
(< x (+ y x)) ==> (< 0 y)
(< (+ x y) x) ==> (< y 0)
(< (+ y x) x) ==> (< y 0)
(< x (+ (+ x y) z)) ==> (< 0 (+ y z))
(< x (+ (+ y x) z)) ==> (< 0 (+ y z))
(< x (+ z (+ x y))) ==> (< 0 (+ z y))
(< x (+ z (+ y x))) ==> (< 0 (+ z y))
(< (+ (+ x y) z) x) ==> (< (+ y z) 0)
(< (+ (+ y x) z) x) ==> (< (+ y z) 0)
(< (+ z (+ x y)) x) ==> (< (+ z y) 0)
(< (+ z (+ y x)) x) ==> (< (+ z y) 0)
(< (+ x y) (+ x z)) ==> (< y z)
(< (+ x y) (+ z x)) ==> (< y z)
(< (+ y x) (+ x z)) ==> (< y z)
(< (+ y x) (+ z x)) ==> (< y z)
(< (+ (+ x y) w) (+ x z)) ==> (< (+ y w) z)
(< (+ (+ y x) w) (+ x z)) ==> (< (+ y w) z)
(< (+ w (+ x y)) (+ x z)) ==> (< (+ y w) z)
(< (+ w (+ y x)) (+ x z)) ==> (< (+ y w) z)
(< (+ (+ x y) w) (+ z x)) ==> (< (+ y w) z)
(< (+ (+ y x) w) (+ z x)) ==> (< (+ y w) z)
(< (+ w (+ x y)) (+ z x)) ==> (< (+ y w) z)
(< (+ w (+ y x)) (+ z x)) ==> (< (+ y w) z)
(< (+ x z) (+ (+ x y) w)) ==> (< z (+ y w))
(< (+ x z) (+ (+ y x) w)) ==> (< z (+ y w))
(< (+ x z) (+ w (+ x y))) ==> (< z (+ y w))
(< (+ x z) (+ w (+ y x))) ==> (< z (+ y w))
(< (+ z x) (+ (+ x y) w)) ==> (< z (+ y w))
(< (+ z x) (+ (+ y x) w)) ==> (< z (+ y w))
(< (+ z x) (+ w (+ x y))) ==> (< z (+ y w))
(< (+ z x) (+ w (+ y x))) ==> (< z (+ y w))
(< (+ (+ x y) w) (+ (+ x z) u)) ==> (< (+ y w) (+ z u))
(< (+ (+ y x) w) (+ (+ x z) u)) ==> (< (+ y w) (+ z u))
(< (+ (+ x y) w) (+ (+ z x) u)) ==> (< (+ y w) (+ z u))
(< (+ (+ y x) w) (+ (+ z x) u)) ==> (< (+ y w) (+ z u))
(< (+ w (+ x y)) (+ (+ x z) u)) ==> (< (+ y w) (+ z u))
(< (+ w (+ y x)) (+ (+ x z) u)) ==> (< (+ y w) (+ z u))
(< (+ w (+ x y)) (+ (+ z x) u)) ==> (< (+ y w) (+ z u))
(< (+ w (+ y x)) (+ (+ z x) u)) ==> (< (+ y w) (+ z u))
(< (+ (+ x y) w) (+ u (+ x z))) ==> (< (+ y w) (+ z u))
(< (+ (+ y x) w) (+ u (+ x z))) ==> (< (+ y w) (+ z u))
(< (+ (+ x y) w) (+ u (+ z x))) ==> (< (+ y w) (+ z u))
(< (+ (+ y x) w) (+ u (+ z x))) ==> (< (+ y w) (+ z u))
(< (+ w (+ x y)) (+ u (+ x z))) ==> (< (+ y w) (+ z u))
(< (+ w (+ y x)) (+ u (+ x z))) ==> (< (+ y w) (+ z u))
(< (+ w (+ x y)) (+ u (+ z x))) ==> (< (+ y w) (+ z u))
(< (+ w (+ y x)) (+ u (+ z x))) ==> (< (+ y w) (+ z u))
(< (min x y) x) ==> (< y x)
(< (min y x) x) ==> (< y x)
(< x (max x y)) ==> (< x y)
(< x (max y x)) ==> (< x y)
(< (min z y) (min x y)) ==> (< z (min x y))
(< (min z y) (min y x)) ==> (< z (min y x))
(< (min y z) (min x y)) ==> (< z (min x y))
(< (min y z) (min y x)) ==> (< z (min y x))
(< (max z y) (max x y)) ==> (< (max z y) x)
(< (max z y) (max y x)) ==> (< (max z y) x)
(< (max y z) (max x y)) ==> (< (max z y) x)
(< (max y z) (max y x)) ==> (< (max z y) x)
(* 0 x) ==> 0
(* 1 x) ==> x
(* x 0) ==> 0
(* x 1) ==> x
(* (- 0 x) y) ==> (- 0 (* x y))
(* x (- 0 y)) ==> (- 0 (* x y))
(* x (* y c0)) ==> (* (* x y) c0)
(* (max x y) (min x y)) ==> (* x y)
(* (max x y) (min y x)) ==> (* y x)
(* x (select y 1 0)) ==> (select y x 0)
(* (select x 1 0) y) ==> (select x y 0)
(select 1 x y) ==> x
(select 0 x y) ==> y
(select x y y) ==> y
(select x (likely y) y) ==> 0_value
(select x y (likely y)) ==> 1_value
(select x (likely_if_innermost y) y) ==> 0_value
(select x y (likely_if_innermost y)) ==> 1_value
(select (!= x y) z w) ==> (select (== x y) w z)
(select (<= x y) z w) ==> (select (< y x) w z)
(select x (select y z w) z) ==> (select (&& x (! y)) w z)
(select x (select y z w) w) ==> (select (&& x y) z w)
(select x y (select z y w)) ==> (select (|| x z) y w)
(select x y (select z w y)) ==> (select (|| x (! z)) y w)
(select x (select x y z) w) ==> (select x y w)
(select x y (select x z w)) ==> (select x y w)
(select x (+ y z) (+ y w)) ==> (+ y (select x z w))
(select x (+ y z) (+ w y)) ==> (+ y (select x z w))
(select x (+ z y) (+ y w)) ==> (+ y (select x z w))
(select x (+ z y) (+ w y)) ==> (+ (select x z w) y)
(select x (- y z) (- y w)) ==> (- y (select x z w))
(select x (- y z) (+ y w)) ==> (+ y (select x (- z) w))
(select x (+ y z) (- y w)) ==> (+ y (select x z (- w)))
(select x (- y z) (+ w y)) ==> (+ y (select x (- z) w))
(select x (+ z y) (- y w)) ==> (+ y (select x z (- w)))
(select x (- z y) (- w y)) ==> (- (select x z w) y)
(select x (* y z) (* y w)) ==> (* y (select x z w))
(select x (* y z) (* w y)) ==> (* y (select x z w))
(select x (* z y) (* y w)) ==> (* y (select x z w))
(select x (* z y) (* w y)) ==> (* (select x z w) y)
(select x (- 0 (* y z)) (* y w)) ==> (* y (select x (- 0 z) w))
(select x (- 0 (* y z)) (* w y)) ==> (* y (select x (- 0 z) w))
(select x (- 0 (* z y)) (* y w)) ==> (* y (select x (- 0 z) w))
(select x (- 0 (* z y)) (* w y)) ==> (* (select x (- 0 z) w) y)
(select x (* y z) (- 0 (* y w))) ==> (* y (select x z (- 0 w)))
(select x (* y z) (- 0 (* w y))) ==> (* y (select x z (- 0 w)))
(select x (* z y) (- 0 (* y w))) ==> (* y (select x z (- 0 w)))
(select x (* z y) (- 0 (* w y))) ==> (* (select x z (- 0 w)) y)
(select x (/ z y) (/ w y)) ==> (/ (select x z w) y)
(select x (+ (+ y z) u) (+ y w)) ==> (+ y (select x (+ z u) w))
(select x (- (+ y z) u) (+ y w)) ==> (+ y (select x (- z u) w))
(select x (+ u (+ y z)) (+ y w)) ==> (+ y (select x (+ u z) w))
(select x (+ y z) (+ (+ y w) u)) ==> (+ y (select x z (+ w u)))
(select x (+ y z) (- (+ y w) u)) ==> (+ y (select x z (- w u)))
(select x (+ y z) (+ u (+ y w))) ==> (+ y (select x z (+ u w)))
(select x (+ (+ y z) u) (+ w y)) ==> (+ y (select x (+ z u) w))
(select x (- (+ y z) u) (+ w y)) ==> (+ y (select x (- z u) w))
(select x (+ u (+ y z)) (+ w y)) ==> (+ y (select x (+ u z) w))
(select x (+ y z) (+ (+ w y) u)) ==> (+ y (select x z (+ w u)))
(select x (+ y z) (- (+ w y) u)) ==> (+ y (select x z (- w u)))
(select x (+ y z) (+ u (+ w y))) ==> (+ y (select x z (+ u w)))
(select x (+ (+ z y) u) (+ y w)) ==> (+ y (select x (+ z u) w))
(select x (- (+ z y) u) (+ y w)) ==> (+ y (select x (- z u) w))
(select x (+ u (+ z y)) (+ y w)) ==> (+ y (select x (+ u z) w))
(select x (+ z y) (+ (+ y w) u)) ==> (+ y (select x z (+ w u)))
(select x (+ z y) (- (+ y w) u)) ==> (+ y (select x z (- w u)))
(select x (+ z y) (+ u (+ y w))) ==> (+ y (select x z (+ u w)))
(select x (+ (+ z y) u) (+ w y)) ==> (+ (select x (+ z u) w) y)
(select x (- (+ z y) u) (+ w y)) ==> (+ (select x (- z u) w) y)
(select x (+ u (+ z y)) (+ w y)) ==> (+ (select x (+ u z) w) y)
(select x (+ z y) (+ (+ w y) u)) ==> (+ (select x z (+ w u)) y)
(select x (+ z y) (- (+ w y) u)) ==> (+ (select x z (- w u)) y)
(select x (+ z y) (+ u (+ w y))) ==> (+ (select x z (+ u w)) y)
(select x (+ y (- z w)) (- u w)) ==> (- (select x (+ y z) u) w)
(select x (+ (- y z) w) (- u z)) ==> (- (select x (+ w y) u) z)
(select x (+ (+ y z) u) y) ==> (+ y (select x (+ z u) 0))
(select x (+ (+ z y) u) y) ==> (+ y (select x (+ z u) 0))
(select x (- (+ y z) u) y) ==> (+ y (select x (- z u) 0))
(select x (- (+ z y) u) y) ==> (+ y (select x (- z u) 0))
(select x (+ u (+ y z)) y) ==> (+ y (select x (+ u z) 0))
(select x (+ u (+ z y)) y) ==> (+ y (select x (+ u z) 0))
(select x y (+ (+ y z) u)) ==> (+ y (select x 0 (+ z u)))
(select x y (+ (+ z y) u)) ==> (+ y (select x 0 (+ z u)))
(select x y (- (+ y z) u)) ==> (+ y (select x 0 (- z u)))
(select x y (- (+ z y) u)) ==> (+ y (select x 0 (- z u)))
(select x y (+ u (+ y z))) ==> (+ y (select x 0 (+ u z)))
(select x y (+ u (+ z y))) ==> (+ y (select x 0 (+ u z)))
(select x (+ (+ y z) w) (+ (+ u y) v)) ==> (+ y (select x (+ z w) (+ u v)))
(select x (+ (- y z) w) (+ (+ u y) v)) ==> (+ y (select x (- w z) (+ u v)))
(select x (+ y (+ z w)) (+ u (+ v w))) ==> (+ w (select x (+ z y) (+ u v)))
(select x (+ y (+ z w)) (+ u (+ v z))) ==> (+ z (select x (+ y w) (+ u v)))
(select x (+ y (+ z w)) (+ u (+ w v))) ==> (+ w (select x (+ z y) (+ u v)))
(select x (+ y (+ z w)) (+ u (+ z v))) ==> (+ z (select x (+ y w) (+ u v)))
(select x (+ y (+ z w)) (+ (+ u w) v)) ==> (+ w (select x (+ z y) (+ u v)))
(select x (+ y (+ z w)) (+ (+ u z) v)) ==> (+ z (select x (+ y w) (+ u v)))
(select x (+ y (+ z w)) (+ (+ w u) v)) ==> (+ w (select x (+ z y) (+ v u)))
(select x (+ y (+ z w)) (+ (+ z u) v)) ==> (+ z (select x (+ y w) (+ v u)))
(select x (+ (+ y z) w) (+ u (+ v y))) ==> (+ y (select x (+ z w) (+ u v)))
(select x (+ (+ y z) w) (+ u (+ v z))) ==> (+ z (select x (+ y w) (+ u v)))
(select x (+ (+ y z) w) (+ u (+ y v))) ==> (+ y (select x (+ z w) (+ u v)))
(select x (+ (+ y z) w) (+ u (+ z v))) ==> (+ z (select x (+ y w) (+ u v)))
(select x (+ (+ y z) w) (+ (+ u y) v)) ==> (+ y (select x (+ z w) (+ u v)))
(select x (+ (+ y z) w) (+ (+ u z) v)) ==> (+ z (select x (+ y w) (+ u v)))
(select x (+ (+ y z) w) (+ (+ y u) v)) ==> (+ y (select x (+ z w) (+ v u)))
(select x (+ (+ y z) w) (+ (+ z u) v)) ==> (+ z (select x (+ y w) (+ v u)))
(select x (select y z w) (select y u w)) ==> (select y (select x z u) w)
(select x (select y z w) (select y z u)) ==> (select y z (select x w u))
(select (< x y) x y) ==> (min x y)
(select (< x y) y x) ==> (max x y)
(select (< x 0) (* x y) 0) ==> (* (min x 0) y)
(select (< x 0) 0 (* x y)) ==> (* (max x 0) y)
(select x (min y w) (min z w)) ==> (min (select x y z) w)
(select x (min y w) (min w z)) ==> (min (select x y z) w)
(select x (min w y) (min z w)) ==> (min w (select x y z))
(select x (min w y) (min w z)) ==> (min w (select x y z))
(select x (max y w) (max z w)) ==> (max (select x y z) w)
(select x (max y w) (max w z)) ==> (max (select x y z) w)
(select x (max w y) (max z w)) ==> (max w (select x y z))
(select x (max w y) (max w z)) ==> (max w (select x y z))
(select x (select y z (min w z)) (min u z)) ==> (min (select x (select y z w) u) z)
(select x (select y (min w z) z) (min u z)) ==> (min (select x (select y w z) u) z)
(select x (min u z) (select y z (min w z))) ==> (min (select x u (select y z w)) z)
(select x (min u z) (select y (min w z) z)) ==> (min (select x u (select y w z)) z)
(select x (select y z (min w z)) (min z u)) ==> (min (select x (select y z w) u) z)
(select x (select y (min w z) z) (min z u)) ==> (min (select x (select y w z) u) z)
(select x (min z u) (select y z (min w z))) ==> (min (select x u (select y z w)) z)
(select x (min z u) (select y (min w z) z)) ==> (min (select x u (select y w z)) z)
(select x (select y z (min z w)) (min u z)) ==> (min (select x (select y z w) u) z)
(select x (select y (min z w) z) (min u z)) ==> (min (select x (select y w z) u) z)
(select x (min u z) (select y z (min z w))) ==> (min (select x u (select y z w)) z)
(select x (min u z) (select y (min z w) z)) ==> (min (select x u (select y w z)) z)
(select x (select y z (min z w)) (min z u)) ==> (min (select x (select y z w) u) z)
(select x (select y (min z w) z) (min z u)) ==> (min (select x (select y w z) u) z)
(select x (min z u) (select y z (min z w))) ==> (min (select x u (select y z w)) z)
(select x (min z u) (select y (min z w) z)) ==> (min (select x u (select y w z)) z)
(select x (select y z (max w z)) (max u z)) ==> (max (select x (select y z w) u) z)
(select x (select y (max w z) z) (max u z)) ==> (max (select x (select y w z) u) z)
(select x (max u z) (select y z (max w z))) ==> (max (select x u (select y z w)) z)
(select x (max u z) (select y (max w z) z)) ==> (max (select x u (select y w z)) z)
(select x (select y z (max w z)) (max z u)) ==> (max (select x (select y z w) u) z)
(select x (select y (max w z) z) (max z u)) ==> (max (select x (select y w z) u) z)
(select x (max z u) (select y z (max w z))) ==> (max (select x u (select y z w)) z)
(select x (max z u) (select y (max w z) z)) ==> (max (select x u (select y w z)) z)
(select x (select y z (max z w)) (max u z)) ==> (max (select x (select y z w) u) z)
(select x (select y (max z w) z) (max u z)) ==> (max (select x (select y w z) u) z)
(select x (max u z) (select y z (max z w))) ==> (max (select x u (select y z w)) z)
(select x (max u z) (select y (max z w) z)) ==> (max (select x u (select y w z)) z)
(select x (select y z (max z w)) (max z u)) ==> (max (select x (select y z w) u) z)
(select x (select y (max z w) z) (max z u)) ==> (max (select x (select y w z) u) z)
(select x (max z u) (select y z (max z w))) ==> (max (select x u (select y z w)) z)
(select x (max z u) (select y (max z w) z)) ==> (max (select x u (select y w z)) z)
(select x (+ y z) y) ==> (+ y (select x z 0))
(select x y (+ y z)) ==> (+ y (select x 0 z))
(select x y 0) ==> (&& x y)
(select x y 1) ==> (|| (! x) y)
(select x 0 y) ==> (&& (! x) y)
(select x 1 y) ==> (|| x y)
(max x x) ==> x
(max (max x y) x) ==> a
(max (max x y) y) ==> a
(max (max (max x y) z) x) ==> a
(max (max (max x y) z) y) ==> a
(max (max (max (max x y) z) w) x) ==> a
(max (max (max (max x y) z) w) y) ==> a
(max (max (max (max (max x y) z) w) u) x) ==> a
(max (max (max (max (max x y) z) w) u) y) ==> a
(max x (max x y)) ==> b
(max x (min x y)) ==> a
(max x (max y x)) ==> b
(max x (min y x)) ==> a
(max (max x y) (min x y)) ==> a
(max (max x y) (min y x)) ==> a
(max (min x y) x) ==> b
(max (min y x) x) ==> b
(max x (min y (min x z))) ==> a
(max x (min y (min z x))) ==> a
(max x (min (min x y) z)) ==> a
(max x (min (min y x) z)) ==> a
(max (min x (min y z)) y) ==> b
(max (min x (min y z)) z) ==> b
(max (min (min x y) z) x) ==> b
(max (min (min x y) z) y) ==> b
(max (max x y) (min x z)) ==> a
(max (max x y) (min y z)) ==> a
(max (max x y) (min z x)) ==> a
(max (max x y) (min z y)) ==> a
(max (select x (max z y) w) z) ==> (max (select x y w) z)
(max (select x (max z y) w) y) ==> (max (select x z w) y)
(max (select x w (max z y)) z) ==> (max (select x w y) z)
(max (select x w (max z y)) y) ==> (max (select x w z) y)
(max (likely x) x) ==> b
(max x (likely x)) ==> a
(max (likely_if_innermost x) x) ==> b
(max x (likely_if_innermost x)) ==> a
(max (max x c0) y) ==> (max (max x y) c0)
(max (max x y) (max x z)) ==> (max (max y z) x)
(max (max y x) (max x z)) ==> (max (max y z) x)
(max (max x y) (max z x)) ==> (max (max y z) x)
(max (max y x) (max z x)) ==> (max (max y z) x)
(max (max x y) (max z w)) ==> (max (max (max x y) z) w)
(max (min x y) (min x z)) ==> (min x (max y z))
(max (min x y) (min z x)) ==> (min x (max y z))
(max (min y x) (min x z)) ==> (min (max y z) x)
(max (min y x) (min z x)) ==> (min (max y z) x)
(max (min (max x y) z) y) ==> (max (min x z) y)
(max (min (max y x) z) y) ==> (max y (min x z))
(max (max x (min y z)) y) ==> (max x y)
(max (max x (min y z)) z) ==> (max x z)
(max (max (min x y) z) x) ==> (max z x)
(max (max (min x y) z) y) ==> (max z y)
(max x (max y (min x z))) ==> (max y x)
(max x (max y (min z x))) ==> (max y x)
(max x (max (min x y) z)) ==> (max x z)
(max x (max (min y x) z)) ==> (max x z)
(max (select x (min y z) w) z) ==> (select x z (max w z))
(max (select x (min z y) w) z) ==> (select x z (max w z))
(max z (select x (min y z) w)) ==> (select x z (max z w))
(max z (select x (min z y) w)) ==> (select x z (max z w))
(max (select x y (min w z)) z) ==> (select x (max y z) z)
(max (select x y (min z w)) z) ==> (select x (max y z) z)
(max z (select x y (min w z))) ==> (select x (max z y) z)
(max z (select x y (min z w))) ==> (select x (max z y) z)
(max (select x y z) (select x w u)) ==> (select x (max y w) (max z u))
(max (+ x y) (+ x z)) ==> (+ x (max y z))
(max (+ x y) (+ z x)) ==> (+ x (max y z))
(max (+ y x) (+ x z)) ==> (+ (max y z) x)
(max (+ y x) (+ z x)) ==> (+ (max y z) x)
(max x (+ x z)) ==> (+ x (max z 0))
(max x (+ z x)) ==> (+ x (max z 0))
(max (+ y x) x) ==> (+ (max y 0) x)
(max (+ x y) x) ==> (+ x (max y 0))
(max (max (+ x y) z) (+ x w)) ==> (max (+ x (max y w)) z)
(max (max z (+ x y)) (+ x w)) ==> (max (+ x (max y w)) z)
(max (max (+ x y) z) (+ w x)) ==> (max (+ x (max y w)) z)
(max (max z (+ x y)) (+ w x)) ==> (max (+ x (max y w)) z)
(max (max (+ y x) z) (+ x w)) ==> (max (+ (max y w) x) z)
(max (max z (+ y x)) (+ x w)) ==> (max (+ (max y w) x) z)
(max (max (+ y x) z) (+ w x)) ==> (max (+ (max y w) x) z)
(max (max z (+ y x)) (+ w x)) ==> (max (+ (max y w) x) z)
(max (+ (+ x w) y) (+ x z)) ==> (+ x (max (+ w y) z))
(max (+ (+ w x) y) (+ x z)) ==> (+ (max (+ w y) z) x)
(max (+ (+ x w) y) (+ z x)) ==> (+ x (max (+ w y) z))
(max (+ (+ w x) y) (+ z x)) ==> (+ (max (+ w y) z) x)
(max (+ (+ x w) y) x) ==> (+ x (max (+ w y) 0))
(max (+ (+ w x) y) x) ==> (+ x (max (+ w y) 0))
(max (+ x y) (+ (+ w x) z)) ==> (+ x (max (+ w z) y))
(max (+ x y) (+ (+ x w) z)) ==> (+ x (max (+ w z) y))
(max (+ y x) (+ (+ w x) z)) ==> (+ (max (+ w z) y) x)
(max (+ y x) (+ (+ x w) z)) ==> (+ (max (+ w z) y) x)
(max x (+ (+ w x) z)) ==> (+ x (max (+ w z) 0))
(max x (+ (+ x w) z)) ==> (+ x (max (+ w z) 0))
(max (- y x) (- z x)) ==> (- (max y z) x)
(max (- x y) (- x z)) ==> (- x (min y z))
(max (- x y) (+ (- z y) w)) ==> (- (max x (+ z w)) y)
(max (- x y) (+ w (- z y))) ==> (- (max x (+ w z)) y)
(max x (- x y)) ==> (- x (min y 0))
(max (- x y) x) ==> (- x (min y 0))
(max x (+ (- x y) z)) ==> (+ x (max (- z y) 0))
(max x (+ z (- x y))) ==> (+ x (max (- z y) 0))
(max x (- (- x y) z)) ==> (- x (min (+ y z) 0))
(max (+ (- x y) z) x) ==> (+ (max (- z y) 0) x)
(max (+ z (- x y)) x) ==> (+ (max (- z y) 0) x)
(max (- (- x y) z) x) ==> (- x (min (+ y z) 0))
(== x 1) ==> x
(== x 0) ==> (! x)
(== (* x y) 0) ==> (|| (== x 0) (== y 0))
(== (select x 0 y) 0) ==> (|| x (== y 0))
(== (select x y 0) 0) ==> (|| (! x) (== y 0))
(== (- (max x y) y) 0) ==> (<= x y)
(== (- (min x y) y) 0) ==> (<= y x)
(== (- (max y x) y) 0) ==> (<= x y)
(== (- (min y x) y) 0) ==> (<= y x)
(== (- y (max x y)) 0) ==> (<= x y)
(== (- y (min x y)) 0) ==> (<= y x)
(== (- y (max y x)) 0) ==> (<= x y)
(== (- y (min y x)) 0) ==> (<= y x)
(== (max x 0) 0) ==> (<= x 0)
(== (min x 0) 0) ==> (<= 0 x)
(== (- c0 x) 0) ==> (== x c0)
(== (- x y) 0) ==> (== x y)
(== x 0) ==> (== x 0)
(/ x 1) ==> x
(/ x 0) ==> 0
(/ x x) ==> 1
(/ 0 x) ==> 0
(/ x x) ==> (select (== x 0) 0 1)
(/ (- (* x c0) y) c0) ==> (+ x (/ (- 0 y) c0))
(/ (- (- (* x c0) y) z) c0) ==> (+ x (/ (- (- 0 y) z) c0))
(/ (+ x y) x) ==> (+ (/ y x) 1)
(/ (+ y x) x) ==> (+ (/ y x) 1)
(/ (- x y) x) ==> (+ (/ (- y) x) 1)
(/ (- y x) x) ==> (- (/ y x) 1)
(/ (+ (+ x y) z) x) ==> (+ (/ (+ y z) x) 1)
(/ (+ (+ y x) z) x) ==> (+ (/ (+ y z) x) 1)
(/ (+ z (+ x y)) x) ==> (+ (/ (+ z y) x) 1)
(/ (+ z (+ y x)) x) ==> (+ (/ (+ z y) x) 1)
(/ (* x y) x) ==> y
(/ (* y x) x) ==> y
(/ (+ (* x y) z) x) ==> (+ y (/ z x))
(/ (+ (* y x) z) x) ==> (+ y (/ z x))
(/ (+ z (* x y)) x) ==> (+ (/ z x) y)
(/ (+ z (* y x)) x) ==> (+ (/ z x) y)
(/ (- (* x y) z) x) ==> (+ y (/ (- z) x))
(/ (- (* y x) z) x) ==> (+ y (/ (- z) x))
(/ (- z (* x y)) x) ==> (- (/ z x) y)
(/ (- z (* y x)) x) ==> (- (/ z x) y)
(/ x (- 1)) ==> (- x)
(&& x 1) ==> a
(&& x 0) ==> b
(&& x x) ==> a
(&& (&& x y) x) ==> a
(&& x (&& x y)) ==> b
(&& (&& x y) y) ==> a
(&& y (&& x y)) ==> b
(&& (&& (&& x y) z) x) ==> a
(&& x (&& (&& x y) z)) ==> b
(&& (&& z (&& x y)) x) ==> a
(&& x (&& z (&& x y))) ==> b
(&& (&& (&& x y) z) y) ==> a
(&& y (&& (&& x y) z)) ==> b
(&& (&& z (&& x y)) y) ==> a
(&& y (&& z (&& x y))) ==> b
(&& (|| x y) x) ==> b
(&& x (|| x y)) ==> a
(&& (|| x y) y) ==> b
(&& y (|| x y)) ==> a
(&& (!= x y) (== x y)) ==> 0
(&& (!= x y) (== y x)) ==> 0
(&& (&& z (!= x y)) (== x y)) ==> 0
(&& (&& z (!= x y)) (== y x)) ==> 0
(&& (&& (!= x y) z) (== x y)) ==> 0
(&& (&& (!= x y) z) (== y x)) ==> 0
(&& (&& z (== x y)) (!= x y)) ==> 0
(&& (&& z (== x y)) (!= y x)) ==> 0
(&& (&& (== x y) z) (!= x y)) ==> 0
(&& (&& (== x y) z) (!= y x)) ==> 0
(&& x (! x)) ==> 0
(&& (! x) x) ==> 0
(&& (<= y x) (< x y)) ==> 0
(&& (< y x) (< x y)) ==> 0
(&& (|| x (&& y z)) y) ==> (&& (|| x z) y)
(&& (|| x (&& z y)) y) ==> (&& (|| x z) y)
(&& y (|| x (&& y z))) ==> (&& y (|| x z))
(&& y (|| x (&& z y))) ==> (&& y (|| x z))
(&& (|| (&& y z) x) y) ==> (&& (|| z x) y)
(&& (|| (&& z y) x) y) ==> (&& (|| z x) y)
(&& y (|| (&& y z) x)) ==> (&& y (|| z x))
(&& y (|| (&& z y) x)) ==> (&& y (|| z x))
(&& (&& x (|| y z)) y) ==> (&& x y)
(&& (&& x (|| z y)) y) ==> (&& x y)
(&& y (&& x (|| y z))) ==> (&& y x)
(&& y (&& x (|| z y))) ==> (&& y x)
(&& (&& (|| y z) x) y) ==> (&& x y)
(&& (&& (|| z y) x) y) ==> (&& x y)
(&& y (&& (|| y z) x)) ==> (&& y x)
(&& y (&& (|| z y) x)) ==> (&& y x)
(&& (|| x y) (|| x z)) ==> (|| x (&& y z))
(&& (|| x y) (|| z x)) ==> (|| x (&& y z))
(&& (|| y x) (|| x z)) ==> (|| x (&& y z))
(&& (|| y x) (|| z x)) ==> (|| x (&& y z))
(&& (< x y) (< x z)) ==> (< x (min y z))
(&& (< y x) (< z x)) ==> (< (max y z) x)
(&& (<= x y) (<= x z)) ==> (<= x (min y z))
(&& (<= y x) (<= z x)) ==> (<= (max y z) x)
(- x 0) ==> x
(- x x) ==> 0
(- (select x y z) (select x w u)) ==> (select x (- y w) (- z u))
(- (select x y z) y) ==> (select x 0 (- z y))
(- (select x y z) z) ==> (select x (- y z) 0)
(- y (select x y z)) ==> (select x 0 (- y z))
(- z (select x y z)) ==> (select x (- z y) 0)
(- (select x (+ y w) z) y) ==> (select x w (- z y))
(- (select x (+ w y) z) y) ==> (select x w (- z y))
(- (select x y (+ z w)) z) ==> (select x (- y z) w)
(- (select x y (+ w z)) z) ==> (select x (- y z) w)
(- (select x (+ y (+ z w)) u) w) ==> (select x (+ y z) (- u w))
(- (select x (+ y (+ z w)) u) z) ==> (select x (+ y w) (- u z))
(- (select x (+ (+ y z) w) u) y) ==> (select x (+ w z) (- u y))
(- (select x (+ (+ y z) w) u) z) ==> (select x (+ w y) (- u z))
(- (select x (+ y z) w) (+ u y)) ==> (- (select x z (- w y)) u)
(- (select x (+ y z) w) (+ u z)) ==> (- (select x y (- w z)) u)
(- (select x (+ y z) w) (+ y u)) ==> (- (select x z (- w y)) u)
(- (select x (+ y z) w) (+ z u)) ==> (- (select x y (- w z)) u)
(- y (select x (+ y w) z)) ==> (- 0 (select x w (- z y)))
(- y (select x (+ w y) z)) ==> (- 0 (select x w (- z y)))
(- z (select x y (+ z w))) ==> (- 0 (select x (- y z) w))
(- z (select x y (+ w z))) ==> (- 0 (select x (- y z) w))
(- (+ x y) x) ==> y
(- (+ x y) y) ==> x
(- x (+ x y)) ==> (- y)
(- y (+ x y)) ==> (- x)
(- (- x y) x) ==> (- y)
(- (+ (select x y z) w) (select x u v)) ==> (+ (select x (- y u) (- z v)) w)
(- (+ w (select x y z)) (select x u v)) ==> (+ (select x (- y u) (- z v)) w)
(- (select x y z) (+ (select x u v) w)) ==> (- (select x (- y u) (- z v)) w)
(- (select x y z) (+ w (select x u v))) ==> (- (select x (- y u) (- z v)) w)
(- (- (select x y z) w) (select x u v)) ==> (- (select x (- y u) (- z v)) w)
(- (+ x c0) y) ==> (+ (- x y) c0)
(- x (- y z)) ==> (+ x (- z y))
(- x (+ y c0)) ==> (- (- x y) c0)
(- (* x y) (* z y)) ==> (* (- x z) y)
(- (* x y) (* y z)) ==> (* (- x z) y)
(- (* y x) (* z y)) ==> (* y (- x z))
(- (* y x) (* y z)) ==> (* y (- x z))
(- (+ u (* x y)) (* z y)) ==> (+ u (* (- x z) y))
(- (+ u (* x y)) (* y z)) ==> (+ u (* (- x z) y))
(- (+ u (* y x)) (* z y)) ==> (+ u (* y (- x z)))
(- (+ u (* y x)) (* y z)) ==> (+ u (* y (- x z)))
(- (- u (* x y)) (* z y)) ==> (- u (* (+ x z) y))
(- (- u (* x y)) (* y z)) ==> (- u (* (+ x z) y))
(- (- u (* y x)) (* z y)) ==> (- u (* y (+ x z)))
(- (- u (* y x)) (* y z)) ==> (- u (* y (+ x z)))
(- (+ (* x y) u) (* z y)) ==> (+ u (* (- x z) y))
(- (+ (* x y) u) (* y z)) ==> (+ u (* (- x z) y))
(- (+ (* y x) u) (* z y)) ==> (+ u (* y (- x z)))
(- (+ (* y x) u) (* y z)) ==> (+ u (* y (- x z)))
(- (- (* x y) u) (* z y)) ==> (- (* (- x z) y) u)
(- (- (* x y) u) (* y z)) ==> (- (* (- x z) y) u)
(- (- (* y x) u) (* z y)) ==> (- (* y (- x z)) u)
(- (- (* y x) u) (* y z)) ==> (- (* y (- x z)) u)
(- (* x y) (+ u (* z y))) ==> (- (* (- x z) y) u)
(- (* x y) (+ u (* y z))) ==> (- (* (- x z) y) u)
(- (* y x) (+ u (* z y))) ==> (- (* y (- x z)) u)
(- (* y x) (+ u (* y z))) ==> (- (* y (- x z)) u)
(- (* x y) (- u (* z y))) ==> (- (* (+ x z) y) u)
(- (* x y) (- u (* y z))) ==> (- (* (+ x z) y) u)
(- (* y x) (- u (* z y))) ==> (- (* y (+ x z)) u)
(- (* y x) (- u (* y z))) ==> (- (* y (+ x z)) u)
(- (* x y) (+ (* z y) u)) ==> (- (* (- x z) y) u)
(- (* x y) (+ (* y z) u)) ==> (- (* (- x z) y) u)
(- (* y x) (+ (* z y) u)) ==> (- (* y (- x z)) u)
(- (* y x) (+ (* y z) u)) ==> (- (* y (- x z)) u)
(- (* x y) (- (* z y) u)) ==> (+ (* (- x z) y) u)
(- (* x y) (- (* y z) u)) ==> (+ (* (- x z) y) u)
(- (* y x) (- (* z y) u)) ==> (+ (* y (- x z)) u)
(- (* y x) (- (* y z) u)) ==> (+ (* y (- x z)) u)
(- (+ x y) (+ x z)) ==> (- y z)
(- (+ x y) (+ z x)) ==> (- y z)
(- (+ y x) (+ x z)) ==> (- y z)
(- (+ y x) (+ z x)) ==> (- y z)
(- (+ (+ x y) z) x) ==> (+ y z)
(- (+ (+ y x) z) x) ==> (+ y z)
(- (+ z (+ x y)) x) ==> (+ z y)
(- (+ z (+ y x)) x) ==> (+ z y)
(- x (+ y (- x z))) ==> (- z y)
(- x (+ (- x y) z)) ==> (- y z)
(- (+ x (- y z)) y) ==> (- x z)
(- (+ (- x y) z) x) ==> (- z y)
(- x (+ y (+ x z))) ==> (- 0 (+ y z))
(- x (+ y (+ z x))) ==> (- 0 (+ y z))
(- x (+ (+ x y) z)) ==> (- 0 (+ y z))
(- x (+ (+ y x) z)) ==> (- 0 (+ y z))
(- (+ x y) (+ z (+ w x))) ==> (- y (+ z w))
(- (+ x y) (+ z (+ w y))) ==> (- x (+ z w))
(- (+ x y) (+ z (+ x w))) ==> (- y (+ z w))
(- (+ x y) (+ z (+ y w))) ==> (- x (+ z w))
(- (+ x y) (+ (+ x z) w)) ==> (- y (+ z w))
(- (+ x y) (+ (+ y z) w)) ==> (- x (+ z w))
(- (+ x y) (+ (+ z x) w)) ==> (- y (+ z w))
(- (+ x y) (+ (+ z y) w)) ==> (- x (+ z w))
(- (- x y) (+ x z)) ==> (- (- 0 y) z)
(- (- x y) (+ z x)) ==> (- (- 0 y) z)
(- (- (+ x y) z) x) ==> (- y z)
(- (- (+ x y) z) y) ==> (- x z)
(- x (min (- x y) 0)) ==> (max x y)
(- x (max (- x y) 0)) ==> (min x y)
(- (+ x y) (min x y)) ==> (max y x)
(- (+ x y) (min y x)) ==> (max y x)
(- (+ x y) (max x y)) ==> (min y x)
(- (+ x y) (max y x)) ==> (min x y)
(- 0 (+ x (- y z))) ==> (- z (+ x y))
(- 0 (+ (- x y) z)) ==> (- y (+ x z))
(- (- (- x y) z) x) ==> (- 0 (+ y z))
(- (max x y) x) ==> (max (- y x) 0)
(- (min x y) x) ==> (min (- y x) 0)
(- (max x y) y) ==> (max (- x y) 0)
(- (min x y) y) ==> (min (- x y) 0)
(- x (min y (- x z))) ==> (max (- x y) z)
(- x (min (- x y) z)) ==> (max y (- x z))
(- x (max y (- x z))) ==> (min (- x y) z)
(- x (max (- x y) z)) ==> (min y (- x z))
(- (min (- x y) 0) x) ==> (- 0 (max x y))
(- (max (- x y) 0) x) ==> (- 0 (min x y))
(- (min x y) (+ x y)) ==> (- 0 (max y x))
(- (min x y) (+ y x)) ==> (- 0 (max x y))
(- (max x y) (+ x y)) ==> (- 0 (min x y))
(- (max x y) (+ y x)) ==> (- 0 (min y x))
(- (* x y) x) ==> (* x (- y 1))
(- (* x y) y) ==> (* (- x 1) y)
(- x (* x y)) ==> (* x (- 1 y))
(- x (* y x)) ==> (* (- 1 y) x)
(- (min (+ x y) z) x) ==> (min (- z x) y)
(- (min (+ y x) z) x) ==> (min (- z x) y)
(- (min z (+ x y)) x) ==> (min (- z x) y)
(- (min z (+ y x)) x) ==> (min (- z x) y)
(- (min x (+ w (+ y z))) z) ==> (min (- x z) (+ w y))
(- (min x (+ w (+ z y))) z) ==> (min (- x z) (+ w y))
(- (min x (+ (+ y z) w)) z) ==> (min (- x z) (+ y w))
(- (min x (+ (+ z y) w)) z) ==> (min (- x z) (+ y w))
(- (min (+ w (+ y z)) x) z) ==> (min (- x z) (+ w y))
(- (min (+ w (+ z y)) x) z) ==> (min (- x z) (+ w y))
(- (min (+ (+ y z) w) x) z) ==> (min (- x z) (+ y w))
(- (min (+ (+ z y) w) x) z) ==> (min (- x z) (+ y w))
(- (min x y) (min y x)) ==> 0
(- (max (+ x y) z) x) ==> (max (- z x) y)
(- (max (+ y x) z) x) ==> (max (- z x) y)
(- (max z (+ x y)) x) ==> (max (- z x) y)
(- (max z (+ y x)) x) ==> (max (- z x) y)
(- (max x (+ w (+ y z))) z) ==> (max (- x z) (+ w y))
(- (max x (+ w (+ z y))) z) ==> (max (- x z) (+ w y))
(- (max x (+ (+ y z) w)) z) ==> (max (- x z) (+ y w))
(- (max x (+ (+ z y) w)) z) ==> (max (- x z) (+ y w))
(- (max (+ w (+ y z)) x) z) ==> (max (- x z) (+ w y))
(- (max (+ w (+ z y)) x) z) ==> (max (- x z) (+ w y))
(- (max (+ (+ y z) w) x) z) ==> (max (- x z) (+ y w))
(- (max (+ (+ z y) w) x) z) ==> (max (- x z) (+ y w))
(- (max x y) (max y x)) ==> 0
(- (+ (min (+ x y) z) w) x) ==> (+ (min (- z x) y) w)
(- (min (+ (+ x y) w) z) x) ==> (min (- z x) (+ y w))
(- (min (min (+ x z) y) w) x) ==> (min (- (min y w) x) z)
(- (min (min y (+ x z)) w) x) ==> (min (- (min y w) x) z)
(- (min (+ (* (+ x y) u) z) w) (* x u)) ==> (min (- w (* x u)) (+ (* y u) z))
(- (min (+ (* (+ y x) u) z) w) (* x u)) ==> (min (- w (* x u)) (+ (* y u) z))
(|| x 1) ==> b
(|| x 0) ==> a
(|| x x) ==> a
(|| (|| x y) x) ==> a
(|| x (|| x y)) ==> b
(|| (|| x y) y) ==> a
(|| y (|| x y)) ==> b
(|| (|| (|| x y) z) x) ==> a
(|| x (|| (|| x y) z)) ==> b
(|| (|| z (|| x y)) x) ==> a
(|| x (|| z (|| x y))) ==> b
(|| (|| (|| x y) z) y) ==> a
(|| y (|| (|| x y) z)) ==> b
(|| (|| z (|| x y)) y) ==> a
(|| y (|| z (|| x y))) ==> b
(|| (&& x y) x) ==> b
(|| x (&& x y)) ==> a
(|| (&& x y) y) ==> b
(|| y (&& x y)) ==> a
(|| (!= x y) (== x y)) ==> 1
(|| (!= x y) (== y x)) ==> 1
(|| (|| z (!= x y)) (== x y)) ==> 1
(|| (|| z (!= x y)) (== y x)) ==> 1
(|| (|| (!= x y) z) (== x y)) ==> 1
(|| (|| (!= x y) z) (== y x)) ==> 1
(|| (|| z (== x y)) (!= x y)) ==> 1
(|| (|| z (== x y)) (!= y x)) ==> 1
(|| (|| (== x y) z) (!= x y)) ==> 1
(|| (|| (== x y) z) (!= y x)) ==> 1
(|| x (! x)) ==> 1
(|| (! x) x) ==> 1
(|| (<= y x) (< x y)) ==> 1
(|| (&& x (|| y z)) y) ==> (|| (&& x z) y)
(|| (&& x (|| z y)) y) ==> (|| (&& x z) y)
(|| y (&& x (|| y z))) ==> (|| y (&& x z))
(|| y (&& x (|| z y))) ==> (|| y (&& x z))
(|| (&& (|| y z) x) y) ==> (|| (&& z x) y)
(|| (&& (|| z y) x) y) ==> (|| (&& z x) y)
(|| y (&& (|| y z) x)) ==> (|| y (&& z x))
(|| y (&& (|| z y) x)) ==> (|| y (&& z x))
(|| (|| x (&& y z)) y) ==> (|| x y)
(|| (|| x (&& z y)) y) ==> (|| x y)
(|| y (|| x (&& y z))) ==> (|| y x)
(|| y (|| x (&& z y))) ==> (|| y x)
(|| (|| (&& y z) x) y) ==> (|| x y)
(|| (|| (&& z y) x) y) ==> (|| x y)
(|| y (|| (&& y z) x)) ==> (|| y x)
(|| y (|| (&& z y) x)) ==> (|| y x)
(|| (&& x y) (&& x z)) ==> (&& x (|| y z))
(|| (&& x y) (&& z x)) ==> (&& x (|| y z))
(|| (&& y x) (&& x z)) ==> (&& x (|| y z))
(|| (&& y x) (&& z x)) ==> (&& x (|| y z))
(|| (< x y) (< x z)) ==> (< x (max y z))
(|| (< y x) (< z x)) ==> (< (min y z) x)
(|| (<= x y) (<= x z)) ==> (<= x (max y z))
(|| (<= y x) (<= z x)) ==> (<= (min y z) x)
(+ x 0) ==> x
(+ 0 x) ==> x
(+ x x) ==> (* x 2)
(+ (select x y z) (select x w u)) ==> (select x (+ y w) (+ z u))
(+ (select x y z) (+ (select x u v) w)) ==> (+ (select x (+ y u) (+ z v)) w)
(+ (select x y z) (+ w (select x u v))) ==> (+ (select x (+ y u) (+ z v)) w)
(+ (select x y z) (- (select x u v) w)) ==> (- (select x (+ y u) (+ z v)) w)
(+ (select x y z) (- w (select x u v))) ==> (+ (select x (- y u) (- z v)) w)
(+ x (* y (- 1))) ==> (- x y)
(+ (* x (- 1)) y) ==> (- y x)
(+ (+ x c0) y) ==> (+ (+ x y) c0)
(+ x (+ y c0)) ==> (+ (+ x y) c0)
(+ (- c0 x) y) ==> (+ (- y x) c0)
(+ (max x (+ (* y c0) z)) (* (- u y) c0)) ==> (+ (max (- x (* y c0)) z) (* u c0))
(+ (- x y) y) ==> x
(+ x (- y x)) ==> y
(+ (+ (- x y) z) y) ==> (+ x z)
(+ (+ z (- x y)) y) ==> (+ z x)
(+ x (+ (- y x) z)) ==> (+ y z)
(+ x (+ z (- y x))) ==> (+ z y)
(+ x (- c0 y)) ==> (+ (- x y) c0)
(+ (- x y) (- y z)) ==> (- x z)
(+ (- x y) (- z x)) ==> (- z y)
(+ (- x y) (+ y z)) ==> (+ x z)
(+ (- x y) (+ z y)) ==> (+ x z)
(+ x (- (- y x) z)) ==> (- y z)
(+ (- (- x y) z) y) ==> (- x z)
(+ x (- y (+ x z))) ==> (- y z)
(+ x (- y (+ z x))) ==> (- y z)
(+ (- x (+ y z)) y) ==> (- x z)
(+ (- x (+ y z)) z) ==> (- x y)
(+ x (- (- 0 y) z)) ==> (- x (+ y z))
(+ (- (- 0 x) y) z) ==> (- z (+ x y))
(+ (* x y) (* z y)) ==> (* (+ x z) y)
(+ (* x y) (* y z)) ==> (* (+ x z) y)
(+ (* y x) (* z y)) ==> (* y (+ x z))
(+ (* y x) (* y z)) ==> (* y (+ x z))
(+ x (* x y)) ==> (* x (+ y 1))
(+ x (* y x)) ==> (* (+ y 1) x)
(+ (* x y) x) ==> (* x (+ y 1))
(+ (min x (- y z)) z) ==> (min (+ x z) y)
(+ (min (- y z) x) z) ==> (min y (+ x z))
(+ z (min x (- y z))) ==> (min (+ z x) y)
(+ z (min (- y z) x)) ==> (min y (+ z x))
(+ z (max x (- y z))) ==> (max (+ z x) y)
(+ z (max (- y z) x)) ==> (max y (+ z x))
(+ (max x (- y z)) z) ==> (max (+ x z) y)
(+ (max (- y z) x) z) ==> (max y (+ x z))
(+ (max x y) (min x y)) ==> (+ x y)
(+ (max x y) (min y x)) ==> (+ x y)
(min x x) ==> x
(min (min x y) x) ==> a
(min (min x y) y) ==> a
(min (min (min x y) z) x) ==> a
(min (min (min x y) z) y) ==> a
(min (min (min (min x y) z) w) x) ==> a
(min (min (min (min x y) z) w) y) ==> a
(min (min (min (min (min x y) z) w) u) x) ==> a
(min (min (min (min (min x y) z) w) u) y) ==> a
(min x (min x y)) ==> b
(min x (max x y)) ==> a
(min x (min y x)) ==> b
(min x (max y x)) ==> a
(min (max x y) (min x y)) ==> b
(min (max x y) (min y x)) ==> b
(min (max x y) x) ==> b
(min (max y x) x) ==> b
(min x (max y (max x z))) ==> a
(min x (max y (max z x))) ==> a
(min x (max (max x y) z)) ==> a
(min x (max (max y x) z)) ==> a
(min (max x (max y z)) y) ==> b
(min (max x (max y z)) z) ==> b
(min (max (max x y) z) x) ==> b
(min (max (max x y) z) y) ==> b
(min (max x y) (min x z)) ==> b
(min (max x y) (min y z)) ==> b
(min (max x y) (min z x)) ==> b
(min (max x y) (min z y)) ==> b
(min (select x (min z y) w) y) ==> (min (select x z w) y)
(min (select x (min z y) w) z) ==> (min (select x y w) z)
(min (select x w (min z y)) y) ==> (min (select x w z) y)
(min (select x w (min z y)) z) ==> (min (select x w y) z)
(min (likely x) x) ==> b
(min x (likely x)) ==> a
(min (likely_if_innermost x) x) ==> b
(min x (likely_if_innermost x)) ==> a
(min (min x c0) y) ==> (min (min x y) c0)
(min (min x y) (min x z)) ==> (min (min y z) x)
(min (min y x) (min x z)) ==> (min (min y z) x)
(min (min x y) (min z x)) ==> (min (min y z) x)
(min (min y x) (min z x)) ==> (min (min y z) x)
(min (min x y) (min z w)) ==> (min (min (min x y) z) w)
(min (max x y) (max x z)) ==> (max x (min y z))
(min (max x y) (max z x)) ==> (max x (min y z))
(min (max y x) (max x z)) ==> (max (min y z) x)
(min (max y x) (max z x)) ==> (max (min y z) x)
(min (max (min x y) z) y) ==> (min (max x z) y)
(min (max (min y x) z) y) ==> (min y (max x z))
(min x (min y (max x z))) ==> (min y x)
(min x (min y (max z x))) ==> (min y x)
(min x (min (max x y) z)) ==> (min x z)
(min x (min (max y x) z)) ==> (min x z)
(min (min x (max y z)) y) ==> (min x y)
(min (min x (max y z)) z) ==> (min x z)
(min (min (max x y) z) x) ==> (min z x)
(min (min (max x y) z) y) ==> (min z y)
(min (select x (max y z) w) z) ==> (select x z (min w z))
(min (select x (max z y) w) z) ==> (select x z (min w z))
(min z (select x (max y z) w)) ==> (select x z (min z w))
(min z (select x (max z y) w)) ==> (select x z (min z w))
(min (select x y (max w z)) z) ==> (select x (min y z) z)
(min (select x y (max z w)) z) ==> (select x (min y z) z)
(min z (select x y (max w z))) ==> (select x (min z y) z)
(min z (select x y (max z w))) ==> (select x (min z y) z)
(min (select x y z) (select x w u)) ==> (select x (min y w) (min z u))
(min (+ x y) (+ x z)) ==> (+ x (min y z))
(min (+ x y) (+ z x)) ==> (+ x (min y z))
(min (+ y x) (+ x z)) ==> (+ (min y z) x)
(min (+ y x) (+ z x)) ==> (+ (min y z) x)
(min x (+ x z)) ==> (+ x (min z 0))
(min x (+ z x)) ==> (+ x (min z 0))
(min (+ y x) x) ==> (+ (min y 0) x)
(min (+ x y) x) ==> (+ x (min y 0))
(min (min (+ x y) z) (+ x w)) ==> (min (+ x (min y w)) z)
(min (min z (+ x y)) (+ x w)) ==> (min (+ x (min y w)) z)
(min (min (+ x y) z) (+ w x)) ==> (min (+ x (min y w)) z)
(min (min z (+ x y)) (+ w x)) ==> (min (+ x (min y w)) z)
(min (min (+ y x) z) (+ x w)) ==> (min (+ (min y w) x) z)
(min (min z (+ y x)) (+ x w)) ==> (min (+ (min y w) x) z)
(min (min (+ y x) z) (+ w x)) ==> (min (+ (min y w) x) z)
(min (min z (+ y x)) (+ w x)) ==> (min (+ (min y w) x) z)
(min (+ (+ x w) y) (+ x z)) ==> (+ x (min (+ w y) z))
(min (+ (+ w x) y) (+ x z)) ==> (+ (min (+ w y) z) x)
(min (+ (+ x w) y) (+ z x)) ==> (+ x (min (+ w y) z))
(min (+ (+ w x) y) (+ z x)) ==> (+ (min (+ w y) z) x)
(min (+ (+ x w) y) x) ==> (+ x (min (+ w y) 0))
(min (+ (+ w x) y) x) ==> (+ x (min (+ w y) 0))
(min (+ x y) (+ (+ w x) z)) ==> (+ x (min (+ w z) y))
(min (+ x y) (+ (+ x w) z)) ==> (+ x (min (+ w z) y))
(min (+ y x) (+ (+ w x) z)) ==> (+ (min (+ w z) y) x)
(min (+ y x) (+ (+ x w) z)) ==> (+ (min (+ w z) y) x)
(min x (+ (+ w x) z)) ==> (+ x (min (+ w z) 0))
(min x (+ (+ x w) z)) ==> (+ x (min (+ w z) 0))
(min (- y x) (- z x)) ==> (- (min y z) x)
(min (- x y) (- x z)) ==> (- x (max y z))
(min (- x y) (+ (- z y) w)) ==> (- (min x (+ z w)) y)
(min (- x y) (+ w (- z y))) ==> (- (min x (+ w z)) y)
(min x (- x y)) ==> (- x (max y 0))
(min (- x y) x) ==> (- x (max y 0))
(min x (+ (- x y) z)) ==> (+ x (min (- z y) 0))
(min x (+ z (- x y))) ==> (+ x (min (- z y) 0))
(min x (- (- x y) z)) ==> (- x (max (+ y z) 0))
(min (+ (- x y) z) x) ==> (+ (min (- z y) 0) x)
(min (+ z (- x y)) x) ==> (+ (min (- z y) 0) x)
(min (- (- x y) z) x) ==> (- x (max (+ y z) 0))
(max x x) ==> x
(max c0 x) ==> (max x c0)
(max (max x c0) y) ==> (max (max x y) c0)
(max x (max y c0)) ==> (max (max x y) c0)
(max (max x y) x) ==> a
(max (max x y) y) ==> a
(max x (max x y)) ==> b
(max y (max x y)) ==> b
(min x x) ==> x
(min c0 x) ==> (min x c0)
(min (min x c0) y) ==> (min (min x y) c0)
(min x (min y c0)) ==> (min (min x y) c0)
(min (min x y) x) ==> a
(min (min x y) y) ==> a
(min x (min x y)) ==> b
(min y (min x y)) ==> b
(- (min x y) (max x z)) ==> (min (- (min x y) (max x z)) 0)
(- (max x y) (min x z)) ==> (max (- (max x y) (min x z)) 0)"#;

const HALIDE_RULES: &str = r#"(max (min (widening_add x y) upper) lower) ==> (saturating_add x y) if is_x_same_int_or_uint
(max (min (widening_sub x y) upper) lower) ==> (saturating_sub x y) if is_x_same_int_or_uint
(rounding_shift_left x y) ==> (rounding_shift_left x y) if is_x_wide_int_or_uint
(widen_right_add (widen_right_add x y) z) ==> (+ x (widening_add y z)) if is_x_same_int_or_uint
(widen_right_sub (widen_right_sub x y) z) ==> (- x (widening_add y z)) if is_x_same_int_or_uint
(widen_right_sub (widen_right_add x y) z) ==> (+ x (widening_sub y z)) if is_x_same_int
(widen_right_add (widen_right_sub x y) z) ==> (+ x (widening_sub z y)) if is_x_same_int
(widen_right_add (+ x (widen_right_add y z)) w) ==> (+ x (+ y (widening_add z w))) if is_x_same_int_or_uint
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
(< x (select y (+ x c0) z)) ==> (&& (! y) (< x z)) if (<= c0 0)
(< x (select y (+ x c0) z)) ==> (|| y (< x z)) if (> c0 0)
(< x (select y z (+ x c0))) ==> (&& y (< x z)) if (<= c0 0)
(< x (select y z (+ x c0))) ==> (|| (! y) (< x z)) if (> c0 0)
(< x (+ (select y (+ x c0) z) c1)) ==> (&& (! y) (< x (+ z c1))) if (<= (+ c0 c1) 0)
(< x (+ (select y (+ x c0) z) c1)) ==> (|| y (< x (+ z c1))) if (> (+ c0 c1) 0)
(< x (+ (select y z (+ x c0)) c1)) ==> (&& y (< x (+ z c1))) if (<= (+ c0 c1) 0)
(< x (+ (select y z (+ x c0)) c1)) ==> (|| (! y) (< x (+ z c1))) if (> (+ c0 c1) 0)
(< (select y (+ x c0) z) x) ==> (&& (! y) (< z x)) if (>= c0 0)
(< (select y (+ x c0) z) x) ==> (|| y (< z x)) if (< c0 0)
(< (select y z (+ x c0)) x) ==> (&& y (< z x)) if (>= c0 0)
(< (select y z (+ x c0)) x) ==> (|| (! y) (< z x)) if (< c0 0)
(< (select y (+ x c0) z) (+ x c1)) ==> (&& (! y) (< z (+ x c1))) if (>= c0 c1)
(< (select y (+ x c0) z) (+ x c1)) ==> (|| y (< z (+ x c1))) if (< c0 c1)
(< (select y z (+ x c0)) (+ x c1)) ==> (&& y (< z (+ x c1))) if (>= c0 c1)
(< (select y z (+ x c0)) (+ x c1)) ==> (|| (! y) (< z (+ x c1))) if (< c0 c1)
(< x (* (/ x c1) c1)) ==> false if (> c1 0)
(< (/ (+ x c1) c0) (/ (+ x c2) c0)) ==> false if (&& (> c0 0) (>= c1 c2))
(< (/ (+ x c1) c0) (/ (+ x c2) c0)) ==> true if (&& (> c0 0) (<= c1 (- c2 c0)))
(< (/ x c0) (/ (+ x c2) c0)) ==> false if (&& (> c0 0) (>= 0 c2))
(< (/ x c0) (/ (+ x c2) c0)) ==> true if (&& (> c0 0) (<= 0 (- c2 c0)))
(< (/ (+ x c1) c0) (/ x c0)) ==> false if (&& (> c0 0) (>= c1 0))
(< (/ (+ x c1) c0) (/ x c0)) ==> true if (&& (> c0 0) (<= c1 (- 0 c0)))
(< (/ (+ x c1) c0) (+ (/ x c0) c2)) ==> false if (&& (> c0 0) (>= c1 (* c2 c0)))
(< (/ (+ x c1) c0) (+ (/ x c0) c2)) ==> true if (&& (> c0 0) (<= c1 (- (* c2 c0) c0)))
(< (/ (+ x c1) c0) (+ (min (/ x c0) y) c2)) ==> false if (&& (> c0 0) (>= c1 (* c2 c0)))
(< (/ (+ x c1) c0) (+ (max (/ x c0) y) c2)) ==> true if (&& (> c0 0) (<= c1 (- (* c2 c0) c0)))
(< (/ (+ x c1) c0) (min (/ (+ x c2) c0) y)) ==> false if (&& (> c0 0) (>= c1 c2))
(< (/ (+ x c1) c0) (max (/ (+ x c2) c0) y)) ==> true if (&& (> c0 0) (<= c1 (- c2 c0)))
(< (/ (+ x c1) c0) (min (/ x c0) y)) ==> false if (&& (> c0 0) (>= c1 0))
(< (/ (+ x c1) c0) (max (/ x c0) y)) ==> true if (&& (> c0 0) (<= c1 (- 0 c0)))
(< (/ (+ x c1) c0) (+ (min y (/ x c0)) c2)) ==> false if (&& (> c0 0) (>= c1 (* c2 c0)))
(< (/ (+ x c1) c0) (+ (max y (/ x c0)) c2)) ==> true if (&& (> c0 0) (<= c1 (- (* c2 c0) c0)))
(< (/ (+ x c1) c0) (min y (/ (+ x c2) c0))) ==> false if (&& (> c0 0) (>= c1 c2))
(< (/ (+ x c1) c0) (max y (/ (+ x c2) c0))) ==> true if (&& (> c0 0) (<= c1 (- c2 c0)))
(< (/ (+ x c1) c0) (min y (/ x c0))) ==> false if (&& (> c0 0) (>= c1 0))
(< (/ (+ x c1) c0) (max y (/ x c0))) ==> true if (&& (> c0 0) (<= c1 (- 0 c0)))
(< (max (/ (+ x c2) c0) y) (/ (+ x c1) c0)) ==> false if (&& (> c0 0) (>= c2 c1))
(< (min (/ (+ x c2) c0) y) (/ (+ x c1) c0)) ==> true if (&& (> c0 0) (<= c2 (- c1 c0)))
(< (max (/ x c0) y) (/ (+ x c1) c0)) ==> false if (&& (> c0 0) (>= 0 c1))
(< (min (/ x c0) y) (/ (+ x c1) c0)) ==> true if (&& (> c0 0) (<= 0 (- c1 c0)))
(< (max y (/ (+ x c2) c0)) (/ (+ x c1) c0)) ==> false if (&& (> c0 0) (>= c2 c1))
(< (min y (/ (+ x c2) c0)) (/ (+ x c1) c0)) ==> true if (&& (> c0 0) (<= c2 (- c1 c0)))
(< (max y (/ x c0)) (/ (+ x c1) c0)) ==> false if (&& (> c0 0) (>= 0 c1))
(< (min y (/ x c0)) (/ (+ x c1) c0)) ==> true if (&& (> c0 0) (<= 0 (- c1 c0)))
(< (max (/ (+ x c2) c0) y) (+ (/ x c0) c1)) ==> false if (&& (> c0 0) (>= c2 (* c1 c0)))
(< (min (/ (+ x c2) c0) y) (+ (/ x c0) c1)) ==> true if (&& (> c0 0) (<= c2 (- (* c1 c0) c0)))
(< (max y (/ (+ x c2) c0)) (+ (/ x c0) c1)) ==> false if (&& (> c0 0) (>= c2 (* c1 c0)))
(< (min y (/ (+ x c2) c0)) (+ (/ x c0) c1)) ==> true if (&& (> c0 0) (<= c2 (- (* c1 c0) c0)))
(< (/ x c0) (min (/ (+ x c2) c0) y)) ==> false if (&& (> c0 0) (< c2 0))
(< (/ x c0) (max (/ (+ x c2) c0) y)) ==> true if (&& (> c0 0) (<= c0 c2))
(< (/ x c0) (min y (/ (+ x c2) c0))) ==> false if (&& (> c0 0) (< c2 0))
(< (/ x c0) (max y (/ (+ x c2) c0))) ==> true if (&& (> c0 0) (<= c0 c2))
(< (max (/ (+ x c2) c0) y) (/ x c0)) ==> false if (&& (> c0 0) (>= c2 0))
(< (min (/ (+ x c2) c0) y) (/ x c0)) ==> true if (&& (> c0 0) (<= (+ c2 c0) 0))
(< (min y (/ (+ x c2) c0)) (/ x c0)) ==> true if (&& (> c0 0) (<= (+ c2 c0) 0))
(< (/ (+ (max x (+ (* y c0) c1)) c2) c0) y) ==> (< (/ (+ x c2) c0) y) if (&& (> c0 0) (< (+ c1 c2) 0))
(< (/ (+ (max x (+ (* y c0) c1)) c2) c0) y) ==> false if (&& (> c0 0) (>= (+ c1 c2) 0))
(< (/ (+ (max x (* y c0)) c1) c0) y) ==> (< (/ (+ x c1) c0) y) if (&& (> c0 0) (< c1 0))
(< (/ (+ (max x (* y c0)) c1) c0) y) ==> false if (&& (> c0 0) (>= c1 0))
(< (/ (+ (max (+ (* x c0) c1) y) c2) c0) x) ==> (< (/ (+ y c2) c0) x) if (&& (> c0 0) (< (+ c1 c2) 0))
(< (/ (+ (max (+ (* x c0) c1) y) c2) c0) x) ==> false if (&& (> c0 0) (>= (+ c1 c2) 0))
(< (/ (+ (max (* x c0) y) c1) c0) x) ==> (< (/ (+ y c1) c0) x) if (&& (> c0 0) (< c1 0))
(< (/ (+ (max (* x c0) y) c1) c0) x) ==> false if (&& (> c0 0) (>= c1 0))
(< (/ (max x (+ (* y c0) c1)) c0) y) ==> (< (/ x c0) y) if (&& (> c0 0) (< c1 0))
(< (/ (max x (+ (* y c0) c1)) c0) y) ==> false if (&& (> c0 0) (>= c1 0))
(< (/ (max x (* y c0)) c20) y) ==> false if (> c0 0)
(< (/ (max (+ (* x c0) c1) y) c0) x) ==> (< (/ y c0) x) if (&& (> c0 0) (< c1 0))
(< (/ (max (+ (* x c0) c1) y) c0) x) ==> false if (&& (> c0 0) (>= c1 0))
(< (/ (max (* x c0) y) c0) x) ==> false if (> c0 0)
(< (/ (+ (min x (+ (* y c0) c1)) c2) c0) y) ==> true if (&& (> c0 0) (< (+ c1 c2) 0))
(< (/ (+ (min x (+ (* y c0) c1)) c2) c0) y) ==> (< (/ (+ x c2) c0) y) if (&& (> c0 0) (>= (+ c1 c2) 0))
(< (/ (+ (min x (* y c0)) c1) c0) y) ==> true if (&& (> c0 0) (< c1 0))
(< (/ (+ (min x (* y c0)) c1) c0) y) ==> (< (/ (+ x c1) c0) y) if (&& (> c0 0) (>= c1 0))
(< (/ (+ (min (+ (* x c0) c1) y) c2) c0) x) ==> true if (&& (> c0 0) (< (+ c1 c2) 0))
(< (/ (+ (min (+ (* x c0) c1) y) c2) c0) x) ==> (< (/ (+ y c2) c0) x) if (&& (> c0 0) (>= (+ c1 c2) 0))
(< (/ (+ (min (* x c0) y) c1) c0) x) ==> true if (&& (> c0 0) (< c1 0))
(< (/ (+ (min (* x c0) y) c1) c0) x) ==> (< (/ (+ y c1) c0) x) if (&& (> c0 0) (>= c1 0))
(< (/ (min x (+ (* y c0) c1)) c0) y) ==> true if (&& (> c0 0) (< c1 0))
(< (/ (min x (+ (* y c0) c1)) c0) y) ==> (< (/ x c0) y) if (&& (> c0 0) (>= c1 0))
(< (/ (min x (* y c0)) c0) y) ==> (< (/ x c0) y) if (> c0 0)
(< (/ (min (+ (* x c0) c1) y) c0) x) ==> true if (&& (> c0 0) (< c1 0))
(< (/ (min (+ (* x c0) c1) y) c0) x) ==> (< (/ y c0) x) if (&& (> c0 0) (>= c1 0))
(< (/ (min (* x c0) y) c0) x) ==> (< (/ y c0) x) if (> c0 0)
(< (min x c0) (min x c1)) ==> false if (>= c0 c1)
(< (min x c0) (+ (min x c1) c2)) ==> false if (&& (>= c0 (+ c1 c2)) (<= c2 0))
(< (max x c0) (max x c1)) ==> false if (>= c0 c1)
(< (max x c0) (+ (max x c1) c2)) ==> false if (&& (>= c0 (+ c1 c2)) (<= c2 0))
(* (slice x c0 c1 c2) (slice y c0 c1 c2)) ==> (slice (* x y) c0 c1 c2) if (&& (> c2 1) (== (lanes_of x) (lanes_of y)))
(* (slice x c0 c1 c2) (* (slice y c0 c1 c2) z)) ==> (* (slice (* x y) c0 c1 c2) z) if (&& (> c2 1) (== (lanes_of x) (lanes_of y)))
(* (slice x c0 c1 c2) (* z (slice y c0 c1 c2))) ==> (* (slice (* x y) c0 c1 c2) z) if (&& (> c2 1) (== (lanes_of x) (lanes_of y)))
(select (< 0 x) (min (* x c0) c1) (* x c0)) ==> (min (* x c0) c1) if (&& (>= c1 0) (>= c0 0))
(select (< x c0) 0 (+ (min x c0) c1)) ==> 0 if (== c0 (- c1))
(select (< 0 x) (/ (+ (* x c0) c1) x) y) ==> (select (< 0 x) (- c0 1) y) if (== c1 (- 1))
(select (< c0 x) (+ x c1) c2) ==> (max (+ x c1) c2) if (|| (== c2 (+ c0 c1)) (== c2 (+ (+ c0 c1) 1)))
(select (< x c0) c1 (+ x c2)) ==> (max (+ x c2) c1) if (|| (== c1 (+ c0 c2)) (== (+ c1 1) (+ c0 c2)))
(select (< c0 x) c1 (+ x c2)) ==> (min (+ x c2) c1) if (|| (== c1 (+ c0 c2)) (== c1 (+ (+ c0 c2) 1)))
(select (< x c0) (+ x c1) c2) ==> (min (+ x c1) c2) if (|| (== c2 (+ c0 c1)) (== (+ c2 1) (+ c0 c1)))
(select (< c0 x) x c1) ==> (max x c1) if (== c1 (+ c0 1))
(select (< x c0) c1 x) ==> (max x c1) if (== (+ c1 1) c0)
(select (< c0 x) c1 x) ==> (min x c1) if (== c1 (+ c0 1))
(select (< x c0) x c1) ==> (min x c1) if (== (+ c1 1) c0)
(max x c0) ==> b if (is_max_value c0)
(max x c0) ==> x if (is_min_value c0)
(max (* (/ x c0) c0) x) ==> b if (> c0 0)
(max x (* (/ x c0) c0)) ==> a if (> c0 0)
(max (min x c0) c1) ==> b if (>= c1 c0)
(max (+ (* (/ (+ x c0) c1) c1) c2) x) ==> a if (&& (> c1 0) (>= (+ c0 c2) (- c1 1)))
(max x (+ (* (/ (+ x c0) c1) c1) c2)) ==> b if (&& (> c1 0) (>= (+ c0 c2) (- c1 1)))
(max (+ (* (/ (+ x c0) c1) c1) c2) x) ==> b if (&& (> c1 0) (<= (+ c0 c2) 0))
(max x (+ (* (/ (+ x c0) c1) c1) c2)) ==> a if (&& (> c1 0) (<= (+ c0 c2) 0))
(max (* (/ x c0) c0) (+ (* (/ x c1) c1) c2)) ==> b if (&& (&& (>= c2 c1) (> c1 0)) (!= c0 0))
(max (+ (* (/ x c1) c1) c2) x) ==> a if (&& (> c1 0) (>= c2 (- c1 1)))
(max x (+ (* (/ x c1) c1) c2)) ==> b if (&& (> c1 0) (>= c2 (- c1 1)))
(max (* (/ (+ x c0) c1) c1) x) ==> a if (&& (> c1 0) (>= c0 (- c1 1)))
(max x (* (/ (+ x c0) c1) c1)) ==> b if (&& (> c1 0) (>= c0 (- c1 1)))
(max (+ (* (/ x c1) c1) c2) x) ==> b if (&& (> c1 0) (<= c2 0))
(max x (+ (* (/ x c1) c1) c2)) ==> a if (&& (> c1 0) (<= c2 0))
(max (* (/ (+ x c0) c1) c1) x) ==> b if (&& (> c1 0) (<= c0 0))
(max x (* (/ (+ x c0) c1) c1)) ==> a if (&& (> c1 0) (<= c0 0))
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
(max (slice x c0 c1 c2) (slice y c0 c1 c2)) ==> (slice (max x y) c0 c1 c2) if (&& (> c2 1) (== (lanes_of x) (lanes_of y)))
(max (slice x c0 c1 c2) (max (slice y c0 c1 c2) z)) ==> (max (slice (max x y) c0 c1 c2) z) if (&& (> c2 1) (== (lanes_of x) (lanes_of y)))
(max (slice x c0 c1 c2) (max z (slice y c0 c1 c2))) ==> (max (slice (max x y) c0 c1 c2) z) if (&& (> c2 1) (== (lanes_of x) (lanes_of y)))
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
(max (* (/ (+ x c0) c1) c1) (+ x c2)) ==> (* (/ (+ x c0) c1) c1) if (&& (> c1 0) (>= (+ c0 1) (+ c1 c2)))
(max (/ (+ x c0) c1) (* (/ (+ x c2) c3) c4)) ==> (/ (+ x c0) c1) if (&& (&& (&& (<= c2 c0) (> c1 0)) (> c3 0)) (== (* c1 c4) c3))
(max (/ (+ x c0) c1) (* (/ (+ x c2) c3) c4)) ==> (* (/ (+ x c2) c3) c4) if (&& (&& (&& (<= (- (+ c0 c3) c1) c2) (> c1 0)) (> c3 0)) (== (* c1 c4) c3))
(max (/ x c1) (* (/ (+ x c2) c3) c4)) ==> (/ x c1) if (&& (&& (&& (<= c2 0) (> c1 0)) (> c3 0)) (== (* c1 c4) c3))
(max (/ x c1) (* (/ (+ x c2) c3) c4)) ==> (* (/ (+ x c2) c3) c4) if (&& (&& (&& (<= (- c3 c1) c2) (> c1 0)) (> c3 0)) (== (* c1 c4) c3))
(max (/ (+ x c0) c1) (* (/ x c3) c4)) ==> (/ (+ x c0) c1) if (&& (&& (&& (<= 0 c0) (> c1 0)) (> c3 0)) (== (* c1 c4) c3))
(max (/ (+ x c0) c1) (* (/ x c3) c4)) ==> (* (/ x c3) c4) if (&& (&& (&& (<= (- (+ c0 c3) c1) 0) (> c1 0)) (> c3 0)) (== (* c1 c4) c3))
(max (/ x c1) (* (/ x c3) c4)) ==> (/ x c1) if (&& (&& (> c1 0) (> c3 0)) (== (* c1 c4) c3))
(== (select x c0 y) 0) ==> (&& (! x) (== y 0)) if (!= c0 0)
(== (select x y c0) 0) ==> (&& x (== y 0)) if (!= c0 0)
(== (+ (max x c0) c1) 0) ==> false if (> (+ c0 c1) 0)
(== (+ (min x c0) c1) 0) ==> false if (< (+ c0 c1) 0)
(== (+ (max x c0) c1) 0) ==> (<= x c0) if (== (+ c0 c1) 0)
(== (+ (min x c0) c1) 0) ==> (<= c0 x) if (== (+ c0 c1) 0)
(== (max x c0) 0) ==> (== x 0) if (< c0 0)
(== (min x c0) 0) ==> (== x 0) if (> c0 0)
(== (max x c0) 0) ==> false if (> c0 0)
(== (min x c0) 0) ==> false if (< c0 0)
(/ (- (* x c1) y) c0) ==> (- (/ (- 0 y) c0) x) if (== (+ c0 c1) 0)
(/ (- (- (* x c1) y) z) c0) ==> (- (/ (- (- 0 y) z) c0) x) if (== (+ c0 c1) 0)
(&& (!= x c0) (== x c1)) ==> b if (!= c0 c1)
(&& (== x c0) (== x c1)) ==> false if (!= c0 c1)
(&& (< c0 x) (< x c1)) ==> false if (&& (! (is_float x)) (<= c1 (+ c0 1)))
(&& (< x c1) (< c0 x)) ==> false if (&& (! (is_float x)) (<= c1 (+ c0 1)))
(&& (<= x c1) (< c0 x)) ==> false if (<= c1 c0)
(&& (<= c0 x) (< x c1)) ==> false if (<= c1 c0)
(&& (<= c0 x) (<= x c1)) ==> false if (< c1 c0)
(&& (<= x c1) (<= c0 x)) ==> false if (< c1 c0)
(- (slice x c0 c1 c2) (slice y c0 c1 c2)) ==> (slice (- x y) c0 c1 c2) if (&& (> c2 1) (== (lanes_of x) (lanes_of y)))
(- (slice x c0 c1 c2) (+ z (slice y c0 c1 c2))) ==> (- (slice (- x y) c0 c1 c2) z) if (&& (> c2 1) (== (lanes_of x) (lanes_of y)))
(- (slice x c0 c1 c2) (+ (slice y c0 c1 c2) z)) ==> (- (slice (- x y) c0 c1 c2) z) if (&& (> c2 1) (== (lanes_of x) (lanes_of y)))
(- (- (slice x c0 c1 c2) z) (slice y c0 c1 c2)) ==> (- (slice (- x y) c0 c1 c2) z) if (&& (> c2 1) (== (lanes_of x) (lanes_of y)))
(- (- z (slice x c0 c1 c2)) (slice y c0 c1 c2)) ==> (- z (slice (+ x y) c0 c1 c2)) if (&& (> c2 1) (== (lanes_of x) (lanes_of y)))
(- (min x y) (min z w)) ==> (- y w) if (can_prove (== (- x y) (- z w)) this)
(- (min x y) (min w z)) ==> (- y w) if (can_prove (== (- x y) (- z w)) this)
(- (min (* x c0) c1) (* (min x c2) c0)) ==> (min (- c1 (* (min x c2) c0)) 0) if (&& (> c0 0) (<= c1 (* c2 c0)))
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
(|| (!= x c0) (== x c1)) ==> a if (!= c0 c1)
(|| (<= x c0) (<= c1 x)) ==> true if (&& (! (is_float x)) (<= c1 (+ c0 1)))
(|| (<= c1 x) (<= x c0)) ==> true if (&& (! (is_float x)) (<= c1 (+ c0 1)))
(|| (<= x c0) (< c1 x)) ==> true if (<= c1 c0)
(|| (<= c1 x) (< x c0)) ==> true if (<= c1 c0)
(|| (< x c0) (< c1 x)) ==> true if (< c1 c0)
(|| (< c1 x) (< x c0)) ==> true if (< c1 c0)
(+ (select x y (+ z c0)) c1) ==> (select x (+ y c1) z) if (== (+ c0 c1) 0)
(+ (slice x c0 c1 c2) (slice y c0 c1 c2)) ==> (slice (+ x y) c0 c1 c2) if (&& (> c2 1) (== (lanes_of x) (lanes_of y)))
(+ (slice x c0 c1 c2) (+ z (slice y c0 c1 c2))) ==> (+ (slice (+ x y) c0 c1 c2) z) if (&& (> c2 1) (== (lanes_of x) (lanes_of y)))
(+ (slice x c0 c1 c2) (+ (slice y c0 c1 c2) z)) ==> (+ (slice (+ x y) c0 c1 c2) z) if (&& (> c2 1) (== (lanes_of x) (lanes_of y)))
(+ (slice x c0 c1 c2) (- z (slice y c0 c1 c2))) ==> (+ (slice (- x y) c0 c1 c2) z) if (&& (> c2 1) (== (lanes_of x) (lanes_of y)))
(+ (slice x c0 c1 c2) (- (slice y c0 c1 c2) z)) ==> (- (slice (+ x y) c0 c1 c2) z) if (&& (> c2 1) (== (lanes_of x) (lanes_of y)))
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
(min (+ (* (/ (+ x c0) c1) c1) c2) x) ==> b if (&& (> c1 0) (>= (+ c0 c2) (- c1 1)))
(min x (+ (* (/ (+ x c0) c1) c1) c2)) ==> a if (&& (> c1 0) (>= (+ c0 c2) (- c1 1)))
(min (+ (* (/ (+ x c0) c1) c1) c2) x) ==> a if (&& (> c1 0) (<= (+ c0 c2) 0))
(min x (+ (* (/ (+ x c0) c1) c1) c2)) ==> b if (&& (> c1 0) (<= (+ c0 c2) 0))
(min (* (/ x c0) c0) (+ (* (/ x c1) c1) c2)) ==> a if (&& (&& (>= c2 c1) (> c1 0)) (!= c0 0))
(min (+ (* (/ x c1) c1) c2) x) ==> b if (&& (> c1 0) (>= c2 (- c1 1)))
(min x (+ (* (/ x c1) c1) c2)) ==> a if (&& (> c1 0) (>= c2 (- c1 1)))
(min (* (/ (+ x c0) c1) c1) x) ==> b if (&& (> c1 0) (>= c0 (- c1 1)))
(min x (* (/ (+ x c0) c1) c1)) ==> a if (&& (> c1 0) (>= c0 (- c1 1)))
(min (+ (* (/ x c1) c1) c2) x) ==> a if (&& (> c1 0) (<= c2 0))
(min x (+ (* (/ x c1) c1) c2)) ==> b if (&& (> c1 0) (<= c2 0))
(min (* (/ (+ x c0) c1) c1) x) ==> a if (&& (> c1 0) (<= c0 0))
(min x (* (/ (+ x c0) c1) c1)) ==> b if (&& (> c1 0) (<= c0 0))
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
(min (slice x c0 c1 c2) (slice y c0 c1 c2)) ==> (slice (min x y) c0 c1 c2) if (&& (> c2 1) (== (lanes_of x) (lanes_of y)))
(min (slice x c0 c1 c2) (min (slice y c0 c1 c2) z)) ==> (min (slice (min x y) c0 c1 c2) z) if (&& (> c2 1) (== (lanes_of x) (lanes_of y)))
(min (slice x c0 c1 c2) (min z (slice y c0 c1 c2))) ==> (min (slice (min x y) c0 c1 c2) z) if (&& (> c2 1) (== (lanes_of x) (lanes_of y)))
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
(min (* (/ (+ x c0) c1) c1) (+ x c2)) ==> (+ x c2) if (&& (> c1 0) (>= (+ c0 1) (+ c1 c2)))
(min (* (min (/ (+ y c0) c1) x) c1) (+ y c2)) ==> (min (* x c1) (+ y c2)) if (&& (> c1 0) (<= (+ c1 c2) (+ c0 1)))
(min (+ (* (min (/ (+ y c0) c1) x) c1) c2) y) ==> (min (+ (* x c1) c2) y) if (&& (> c1 0) (<= c1 (+ (+ c0 c2) 1)))
(min (* (min (/ (+ y c0) c1) x) c1) y) ==> (min (* x c1) y) if (&& (> c1 0) (<= c1 (+ c0 1)))
(min (/ (+ x c0) c1) (* (/ (+ x c2) c3) c4)) ==> (/ (+ x c0) c1) if (&& (&& (&& (<= (- (+ c0 c3) c1) c2) (> c1 0)) (> c3 0)) (== (* c1 c4) c3))
(min (/ (+ x c0) c1) (* (/ (+ x c2) c3) c4)) ==> (* (/ (+ x c2) c3) c4) if (&& (&& (&& (<= c2 c0) (> c1 0)) (> c3 0)) (== (* c1 c4) c3))
(min (/ x c1) (* (/ (+ x c2) c3) c4)) ==> (/ x c1) if (&& (&& (&& (<= (- c3 c1) c2) (> c1 0)) (> c3 0)) (== (* c1 c4) c3))
(min (/ x c1) (* (/ (+ x c2) c3) c4)) ==> (* (/ (+ x c2) c3) c4) if (&& (&& (&& (<= c2 0) (> c1 0)) (> c3 0)) (== (* c1 c4) c3))
(min (/ (+ x c0) c1) (* (/ x c3) c4)) ==> (/ (+ x c0) c1) if (&& (&& (&& (<= (- (+ c0 c3) c1) 0) (> c1 0)) (> c3 0)) (== (* c1 c4) c3))
(min (/ (+ x c0) c1) (* (/ x c3) c4)) ==> (* (/ x c3) c4) if (&& (&& (&& (<= 0 c0) (> c1 0)) (> c3 0)) (== (* c1 c4) c3))
(min (/ x c1) (* (/ x c3) c4)) ==> (* (/ x c3) c4) if (&& (&& (> c1 0) (> c3 0)) (== (* c1 c4) c3))
(- (min (+ x c0) y) (select z (+ (min x y) c1) x)) ==> (select z (- (max (min (- y x) c0) 0) c1) (min (- y x) c0)) if (> c0 0)
(- (min y (+ x c0)) (select z (+ (min y x) c1) x)) ==> (select z (- (max (min (- y x) c0) 0) c1) (min (- y x) c0)) if (> c0 0)"#;

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

const CHOMPY_RULES_FOR_DEBUGGING: &str = r#"(> ?a ?a) ==> 0
(- ?a ?a) ==> 0
(< ?a ?a) ==> 0
(+ 0 ?a) ==> ?a
(+ ?a 0) ==> ?a
(- ?a 0) ==> ?a
(< ?a ?b) ==> (> ?b ?a)
(+ ?a ?b) ==> (+ ?b ?a)
(< ?a 1) ==> (< ?a 0) if  (!= ?a 0)
(< ?a 1) ==> 1 if (<= ?a 0)
(< 1 ?a) ==> 0 if (<= ?a 0)
(< ?a 1) ==> 0 if (< 0 ?a)
?a ==> (< 1 ?a) if  (== ?a 0)
(< ?b ?a) ==> 1 if (< ?b ?a)
(< ?b ?a) ==> 0 if (<= ?a ?b)
?a ==> 0 if (== ?a 0)
(- ?b ?a) ==> 0 if (&& 1 (== ?a ?b))
(- ?b ?a) ==> 0 if (== ?b ?a)
(+ ?b ?a) ==> (+ ?b ?b) if (&& 1 (== ?b ?a))
(+ 1 (+ ?a 1)) ==> (+ ?a (+ 1 1))
(< (- ?a ?b) ?a) ==> (- 1 (< ?b 1))
(< ?a (+ ?b ?a)) ==> (- 1 (< ?b 1))
(< ?b (< ?b ?a)) ==> (< ?b (< 0 ?a))
(< (< ?b ?a) ?a) ==> (< (< ?b 1) ?a)
(< (< ?a ?b) ?a) ==> (< (< 1 ?b) ?a)
(< ?a (+ ?b ?a)) ==> (< (- 0 ?b) ?b)
(< ?a (< ?b ?a)) ==> (< ?a (< ?b 0))
(< ?a 1) ==> (- 1 (< 0 ?a))
(- ?c (- ?b ?a)) ==> (- (+ ?c ?a) ?b)
(< 1 ?a) ==> (< (< 0 ?a) ?a)
(< 0 ?a) ==> (< (< ?a 0) ?a)
(< 0 ?a) ==> (< (- 1 ?a) ?a)
(< 0 ?a) ==> (< (< 1 ?a) ?a)
(< 0 ?a) ==> (< 1 (+ ?a ?a))
(- (+ ?b ?a) ?a) ==> ?b
(+ ?a (- ?b ?a)) ==> ?b
(< 0 1) ==> 1
(< 1 0) ==> 0
(< (- ?a 1) ?a) ==> 1
(< ?a (+ ?a 1)) ==> 1
(< (+ ?a 1) ?a) ==> 0
(< ?a (- ?a 1)) ==> 0
(< (< ?b ?a) 0) ==> 0
(< 1 (< ?b ?a)) ==> 0
(- ?a (- 0 ?b)) ==> (+ ?b ?a)
(- 0 (- ?a ?b)) ==> (- ?b ?a)
(< 0 (- ?a ?b)) ==> (< ?b ?a)
(< 0 (< ?b ?a)) ==> (< ?b ?a)
(< ?a (- 1 ?a)) ==> (< ?a 1)
(< (+ ?a ?a) 1) ==> (< ?a 1)
(< ?a (< ?a 1)) ==> (< ?a 1)
(< ?a (< 1 ?a)) ==> (< ?a 0)
(< (+ ?a ?a) 0) ==> (< ?a 0)
(< ?a (< 0 ?a)) ==> (< ?a 0)
(< ?a (< ?a 0)) ==> (< ?a 0)
(< (< ?a 1) ?a) ==> (< 0 ?a)
(< ?c (< ?b ?a)) ==> (< ?c 0) if (!= ?c 0)
(< ?b ?a) ==> (< ?b (+ ?a 1)) if  (!= ?b ?a)
(< ?a (< ?b ?a)) ==> 1 if (< ?a 0)
(- ?a) ==> ?a if  (== ?a 0)
(- (- ?a)) ==> ?a
(/ ?a 1) ==> ?a
(* ?a 1) ==> ?a
(* 1 ?a) ==> ?a
(- 0 ?a) ==> (- ?a)
(* ?a 0) ==> 0
(* 0 ?a) ==> 0
(/ 0 ?a) ==> 0
(/ ?a 0) ==> 0
(* ?a ?b) ==> (* ?b ?a)
(/ ?a ?a) ==> 1 if (!= ?a 0)
(- ?b ?a) ==> 0 if (== ?a ?b)
(- ?b ?a) ==> 0 if (&& 1 (== ?b ?a))
(/ ?b (- ?a)) ==> (- (/ ?b ?a))
(/ (- ?b) ?a) ==> (- (/ ?b ?a))
(/ ?a (- ?a)) ==> (/ (- ?a) ?a)
(- (/ ?a ?a)) ==> (/ (- ?a) ?a)
(- (* ?b ?a)) ==> (* ?a (- ?b))
(- ?b ?a) ==> (- (- ?a ?b))
(- ?a) ==> (/ ?a (- 1))
(- ?a) ==> (* ?a (- 1))
(+ ?b ?a) ==> (- ?a (- ?b))
(+ ?a ?a) ==> (- ?a (- ?a))
(+ ?a (- ?a)) ==> 0
(/ ?b ?a) ==> (/ ?a ?a) if (== ?b ?a)
(/ ?a ?b) ==> (/ ?a ?a) if (&& 1 (== ?a ?b))
(* ?b (/ 1 ?a)) ==> (/ ?b (/ 1 ?a))
(/ 1 (* ?a ?a)) ==> (/ ?a (/ 1 ?a))
(* ?a (/ 1 ?a)) ==> (/ ?a (/ 1 ?a))
(+ ?b (* ?b ?a)) ==> (* ?b (+ ?a 1))
(- (* ?b ?a) ?a) ==> (* ?a (- ?b 1))
(/ 1 ?a) ==> (/ 1 (/ 1 ?a))
(+ ?c (- ?b ?a)) ==> (- (+ ?b ?c) ?a)
(+ ?b (- ?b ?a)) ==> (- (+ ?b ?b) ?a)
(/ ?c (* ?b ?a)) ==> (/ (/ ?c ?a) ?b)
(* ?c (* ?b ?a)) ==> (* ?b (* ?c ?a))
(- (- ?c ?b) ?a) ==> (- ?c (+ ?a ?b))
(* ?b (/ ?a ?a)) ==> (/ (* ?a ?b) ?a)
(/ (* ?a ?b) ?a) ==> (/ ?b (/ ?a ?a))
(/ ?b (* ?b ?a)) ==> (/ (/ ?b ?a) ?b)
(+ ?c (+ ?b ?a)) ==> (+ ?a (+ ?c ?b))
(/ ?a (* ?b ?a)) ==> (/ (/ ?a ?a) ?b)
(+ ?b (+ ?a ?a)) ==> (+ ?a (+ ?a ?b))
(* ?b (* ?a ?a)) ==> (* ?a (* ?a ?b))
(+ ?a ?a) ==> (* ?a (+ 1 1))
(/ 1 ?a) ==> (/ ?a (* ?a ?a))
(/ 1 ?a) ==> (/ (/ ?a ?a) ?a)
(/ ?a ?a) ==> (/ 1 (/ ?a ?a))
(/ 1 (+ ?a ?a)) ==> 0
(/ ?a (+ ?a ?a)) ==> 0
?a ==> (/ ?a (/ ?a ?a))
?a ==> (/ (* ?a ?a) ?a)
?a ==> (* ?a (/ ?a ?a))
(/ (- 1 ?a) ?a) ==> (- (/ 1 ?a) 1) if  (< ?a 0)
(+ 1 (/ 1 ?a)) ==> (/ (+ ?a 1) ?a) if  (< 0 ?a)
(- (/ 1 ?a)) ==> (* ?a (/ 1 ?a)) if  (< ?a 0)
(/ (+ ?a 1) ?a) ==> 0 if (<= ?a 0)
(/ ?a (- ?a 1)) ==> 0 if (<= ?a 0)
(/ ?a (+ ?a 1)) ==> 0 if (<= 0 ?a)
(/ (- 1 ?a) ?a) ==> 0 if (<= 0 ?a)
(- (/ ?a ?a) 1) ==> (/ 1 (- ?a 1)) if  (&& 1 (<= ?a 0))
(- (/ 1 ?a)) ==> (* ?a (/ 1 ?a)) if  (&& 1 (<= ?a 0))
(/ 1 ?a) ==> (* ?a (/ 1 ?a)) if  (&& 1 (<= 0 ?a))
(min ?b ?a) ==> (min ?a ?b)
(max ?b ?a) ==> (max ?a ?b)
?a ==> (max ?a ?a)
?a ==> (min ?a ?a)
(min ?a ?b) ==> ?a if (<= ?a ?b)
(max ?b ?a) ==> ?b if (<= ?a ?b)
(min ?c (min ?b ?a)) ==> (min ?a (min ?b ?c))
(max ?c (max ?b ?a)) ==> (max ?b (max ?c ?a))
(min ?b ?a) ==> (min ?b (min ?b ?a))
(max ?b ?a) ==> (max ?b (max ?b ?a))
(min ?a (max ?b ?a)) ==> ?a
(max ?a (min ?b ?a)) ==> ?a
(max ?c (min ?b ?a)) ==> (min ?a (max ?c ?b)) if  (<= ?c ?a)
(min ?c (max ?b ?a)) ==> (max (min ?a ?c) (min ?b ?c))
(max ?b (min ?a ?c)) ==> (min (max ?b ?c) (max ?b ?a))
(max ?b (min ?a ?c)) ==> (max ?b (min ?c (max ?b ?a)))
?a ==> (min ?a 1) if  (<= ?a 0)
?a ==> (max ?a 1) if  (< 0 ?a)
(max ?a (+ ?b ?a)) ==> (+ ?a (max ?b 0))
(min ?a (+ ?b ?a)) ==> (+ ?a (min ?b 0))
?a ==> (min ?a (+ ?a 1))
0 ==> (min 0 1)
(+ ?a (max ?a 1)) ==> (max (+ ?a ?a) 1) if  (<= 0 ?a)
(min ?a 1) ==> (min (+ ?a ?a) 1) if  (<= 0 ?a)
(max ?b (+ ?a 1)) ==> ?b if (< ?a ?b)
(== ?a (min ?b ?a)) ==> (== (min ?b ?a) ?a)
(== ?a 1) ==> (== 1 ?a)
(== 0 ?a) ==> (== ?a 0)
0 ==> (== 1 0)
0 ==> (== 0 1)
(== ?a ?a) ==> 1
(== (min ?c ?a) (min ?b ?a)) ==> (== ?a (min ?c ?a)) if (< ?c ?b)
(== 1 (min ?b ?a)) ==> 0 if (<= ?a 0)
(== ?b (min ?c ?a)) ==> (== ?b ?a) if (< ?a ?b)
(== (min ?c ?b) ?a) ==> (== ?b ?a) if (< ?a ?c)
(== ?c (min ?b ?a)) ==> (== ?c ?a) if (< ?c ?b)
(== 1 ?a) ==> 0 if (<= ?a 0)
(== (min ?c ?b) ?a) ==> 0 if (< ?b ?a)
(== ?b ?a) ==> 0 if (!= ?b ?a)
(== ?a (max ?b ?a)) ==> (== (max ?b ?a) ?a)
(== (max ?c ?a) (max ?b ?a)) ==> (== ?a (max ?c ?a)) if (< ?b ?c)
(== 1 (max ?b ?a)) ==> (== 1 ?a) if (<= ?b 0)
(== ?b (max ?c ?a)) ==> (== ?b ?a) if (< ?b ?a)
(== ?b (max ?a ?c)) ==> (== ?b ?a) if (< ?c ?b)
(== (max ?c ?b) ?a) ==> (== ?b ?a) if (< ?c ?a)
(== (max ?c ?b) ?a) ==> 0 if (< ?a ?b)
?a ==> (min ?a (* ?a ?a))
(min ?b (* ?a ?a)) ==> ?b if (<= ?b 0)
(min ?b (* ?a (max ?b ?a))) ==> (min ?b (* ?b (min ?b ?a)))
(* ?b ?a) ==> (* (min ?b ?a) (max ?b ?a))
(min ?c (* ?b (max ?b ?a))) ==> (min ?c (* ?a (min ?b ?a))) if  (<= ?c 0)
(min ?a (* ?b (* ?a ?a))) ==> (min ?a (* ?b (max ?a ?b))) if  (<= 0 ?b)
(min ?b (max ?a (* ?b ?a))) ==> (min ?b (* ?b (* ?b ?a))) if  (<= 0 ?a)
(* (max ?b ?a) (min ?b ?c)) ==> (* ?b (min ?c (max ?b ?a))) if  (< ?a ?c)
(* ?c (max ?b ?a)) ==> (min (* ?c ?b) (* ?c ?a)) if  (<= ?c 0)
(* ?b (min ?c ?a)) ==> (max (* ?c ?b) (* ?b ?a)) if  (<= ?b 0)
(min ?b (* ?b ?a)) ==> (min ?b (* ?a (min ?b ?a))) if  (<= ?b 0)
(min ?b (* ?a ?a)) ==> (min ?b (* ?a (min ?a ?b))) if  (<= ?a 0)
(* ?a (max ?b ?a)) ==> (min (* ?b ?a) (* ?a ?a)) if  (<= ?a 0)
(* ?a (min ?b ?a)) ==> (max (* ?b ?a) (* ?a ?a)) if  (<= ?a 0)
(min ?a (* ?b ?a)) ==> (min ?a (* ?a (max ?b ?a))) if  (<= ?a 0)
(min ?a (* ?b ?a)) ==> (min ?a (* ?a (min ?b ?a))) if  (<= ?b 0)
(min ?b (* ?b ?a)) ==> (min ?b (* ?b (max ?b ?a))) if  (< 0 ?a)
(* ?c (max ?b ?a)) ==> (max (* ?c ?b) (* ?c ?a)) if  (<= 0 ?c)
(min ?b (* ?a ?a)) ==> (min ?b (* ?a (min ?b ?a))) if  (<= 0 ?b)
(* ?a (max ?b ?a)) ==> (max (* ?b ?a) (* ?a ?a)) if  (<= 0 ?a)
(* ?b (min ?c ?a)) ==> (min (* ?c ?b) (* ?b ?a)) if  (<= 0 ?b)
(max ?a (* ?b (* ?a ?a))) ==> ?a if (< ?b 0)
?a ==> (max ?a (* ?a (* ?a ?a))) if  (<= ?a 0)
(min ?a (* ?a (min ?a ?b))) ==> ?a if (<= ?a 0)
(min ?a (max ?b (* ?a ?b))) ==> ?a if (<= ?a 0)
(min ?a (* ?a (max ?b ?a))) ==> ?a if (<= ?b 0)
(min ?b (* ?a (max ?b ?a))) ==> ?b if (< 0 ?a)
(min ?a (* ?b (* ?a ?a))) ==> ?a if (< 0 ?b)
(min ?a (max ?b (* ?b ?a))) ==> ?a if (< 0 ?b)
(min ?a (* ?a (max ?b ?a))) ==> ?a if (<= 0 ?a)
?a ==> (min ?a (* ?a (* ?a ?a))) if  (<= 0 ?a)
(max ?b ?a) ==> ?b if (== ?b ?a)
(max ?b ?a) ==> ?b if (< ?a ?b)
(* (min ?c ?a) (max ?b ?a)) ==> (* ?a (max ?b (min ?c ?a))) if  (&& 1 (<= ?b ?c))
(min ?b (* ?b ?a)) ==> (min ?b (* ?a (max ?b ?a))) if  (&& 1 (<= 0 ?b))
(max ?b ?a) ==> ?a if (&& 1 (<= ?b ?a))"#;

// Stiches together the against_total rules and the base_conditional rules:
// given this combination of rules, how many of `against_conditional` can we derive?
fn run_derivability_tests<L: SynthLanguage>(
    base_conditional: &Ruleset<L>,
    against_conditional: &Ruleset<L>,
    against_total: &Ruleset<L>,
    implications: &ImplicationSet<L>,
) -> DerivabilityResult<L> {
    let impl_rules = implications.to_egg_rewrites();

    println!("running derivability test...");

    assert!(base_conditional.iter().all(|r| r.cond.is_some()));
    assert!(against_conditional.iter().all(|r| r.cond.is_some()));
    assert!(against_total.iter().all(|r| r.cond.is_none()));

    let mut base = base_conditional.clone();
    base.extend(against_total.clone());

    let (can, cannot) = base.derive(
        ruler::DeriveType::LhsAndRhs,
        against_conditional,
        Limits::deriving(),
        Some(&impl_rules),
    );

    DerivabilityResult { can, cannot }
}

fn read_rules<L: SynthLanguage>(rules: &str) -> Ruleset<L> {
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
            _ => println!("Unable to parse single rule: {}", rule),
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

        if candidates.contains(desired_rule) {
            can.add(rule.clone());
        } else {
            cannot.add(rule.clone());
        }
    }

    (can, cannot)
}

// A simple derivability test. How many other rules can Chompy's rulesets derive?
fn derivability_test<L: SynthLanguage>(
    against_total: &Ruleset<L>,
    against_conditional: &Ruleset<L>,
    id: &str,
) {
    // Don't run this test as part of the "unit tests" thing in CI.
    if std::env::var("SKIP_RECIPES").is_ok() {
        return;
    }

    // root directory: "out/derive.json"
    let binding = std::env::var("OUT_DIR").expect("OUT_DIR environment variable not set")
        + &format!("/derive-{id}.json").to_string();
    let out_path: &Path = Path::new(&binding);

    // let chompy_rules = og_recipe();
    let chompy_rules = read_rules(CHOMPY_RULES_FOR_DEBUGGING);
    let chompy_conditional = chompy_rules.partition(|r| r.cond.is_some()).0;

    let mut all_conditions: Vec<_> = against_conditional
        .iter()
        .chain(chompy_conditional.iter())
        .filter_map(|r| {
            r.cond.as_ref().and_then(|c| {
                Assumption::new(
                    L::generalize(
                        &L::instantiate(&c.chop_assumption()),
                        &mut Default::default(),
                    )
                    .to_string(),
                )
                .ok()
            })
        })
        .collect();

    all_conditions.sort_by(|a, b| a.to_string().cmp(&b.to_string()));
    all_conditions.dedup();

    println!("conditions: {}", all_conditions.len());
    for c in &all_conditions {
        println!("  {c}");
    }

    let implication_rules: ImplicationSet<L> = pairwise_implication_building(&all_conditions);

    // see how many against rules we can derive, given the same
    // total against rules.
    let forward_result = run_derivability_tests(
        &chompy_conditional,
        against_conditional,
        against_total,
        &implication_rules,
    );
    let backward_result = run_derivability_tests(
        &against_conditional,
        &chompy_conditional,
        against_total,
        &implication_rules,
    );

    let to_json = |result: DerivabilityResult<L>| {
        // remove all the total rules.

        serde_json::json!({
            "can": result.can.iter().filter_map(|r| {
                if r.cond.is_some() {
                    Some(r.to_string())
                } else {
                    None
                }
            }).collect::<Vec<_>>(),
            "cannot": result.cannot.iter().filter_map(|r| {
                if r.cond.is_some() {
                    Some(r.to_string())
                } else {
                    None
                }
            }).collect::<Vec<_>>(),

        })
    };

    let to_write = serde_json::json!({
        "forwards": to_json(forward_result),
        "backwards": to_json(backward_result),
    });
    std::fs::write(out_path, to_write.to_string())
        .expect("Failed to write derivability results to file");
}

#[cfg(test)]
pub mod halide_derive_tests {
    use std::path::Path;

    use ruler::{
        conditions::{generate::compress, implication_set::run_implication_workload},
        enumo::Metric,
        halide::og_recipe,
        recipe_utils::{recursive_rules_cond, run_workload, Lang},
    };

    use super::*;

    #[test]
    fn chompy_vs_caviar() {
        let all_caviar_rules: Ruleset<Pred> = read_rules(CAVIAR_RULES);
        let caviar_conditional_rules = all_caviar_rules.partition(|r| r.cond.is_some()).0;
        let caviar_total_rules = all_caviar_rules.partition(|r| r.cond.is_none()).0;
        derivability_test(&caviar_total_rules, &caviar_conditional_rules, "caviar");
    }

    #[test]
    fn chompy_vs_halide() {
        let all_halide_rules: Ruleset<Pred> = read_rules(HALIDE_RULES);
        let halide_conditional_rules = all_halide_rules.partition(|r| r.cond.is_some()).0;
        // let halide_total_rules = all_halide_rules.partition(|r| r.cond.is_none()).0;

        let chompy_total_rules = read_rules(CHOMPY_RULES_FOR_DEBUGGING)
            .partition(|r| r.cond.is_none())
            .0;

        derivability_test(&chompy_total_rules, &halide_conditional_rules, "halide");
    }

    // A test to see if we can correctly choose all Caviar handwritten rules
    // as candidates.
    #[test]
    fn synthesize_all_caviar_as_candidates() {
        // Don't run this test as part of the "unit tests" thing in CI.
        if std::env::var("SKIP_RECIPES").is_ok() {
            return;
        }

        let caviar_rules: Ruleset<Pred> = read_rules(CAVIAR_RULES);
        let caviar_conditional_rules = caviar_rules.partition(|r| r.cond.is_some()).0;
        let (_, cannot) = can_synthesize_all(caviar_conditional_rules.clone());
        // This is a magic number for now, but later we'll document specific
        // rules we can't derive along with why.
        assert_eq!(cannot.len(), 7);
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
            .plug("V", &Workload::new(&["a", "b", "c", "0"]));

        let rules = run_workload(
            cond_workload.clone(),
            None,
            Ruleset::default(),
            ImplicationSet::default(),
            Limits::synthesis(),
            Limits::minimize(),
            true,
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
        );

        all_rules.extend(min_max_add_rules);

        let min_max_sub_rules = recursive_rules_cond(
            Metric::Atoms,
            5,
            Lang::new(&[], &["a", "b", "c"], &[&[], &["min", "max", "-"]]),
            all_rules.clone(),
            implications.clone(),
            cond_wkld.clone(),
        );

        all_rules.extend(min_max_sub_rules);

        let min_max_mul_rules = recursive_rules_cond(
            Metric::Atoms,
            7,
            Lang::new(&[], &["a", "b", "c"], &[&[], &["min", "max", "*"]]),
            all_rules.clone(),
            implications.clone(),
            cond_wkld.clone(),
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
}
