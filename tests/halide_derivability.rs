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

const CHOMPY_RULES: &str = r#"
(== ?a ?b) <=> (== ?b ?a)
(!= ?a ?b) <=> (!= ?b ?a)
(<= ?a ?a) ==> 1
(== ?a ?a) ==> 1
(< ?a ?a) ==> 0
(!= ?a ?a) ==> 0
(< ?b ?a) <=> (!= ?b ?a) if  (<= ?b ?a)
(<= ?b ?a) <=> (== ?b ?a) if  (<= ?a ?b)
(<= ?b ?a) <=> (< ?b ?a) if  (!= ?b ?a)
(< ?b ?a) ==> 1 if (< ?b ?a)
(<= ?b ?a) ==> 0 if (< ?a ?b)
(!= ?b ?a) ==> 1 if (!= ?b ?a)
(== ?b ?a) ==> 0 if (!= ?b ?a)
(< ?b ?a) ==> 0 if (<= ?a ?b)
(<= ?b ?a) ==> 1 if (<= ?b ?a)
(== ?b ?a) <=> (&& (<= ?b ?a) (<= ?a ?b))
(&& (<= ?b ?a) (<= ?b ?a)) <=> (<= ?b ?a)
(&& (< ?b ?a) (< ?b ?a)) <=> (< ?b ?a)
(< ?b ?a) <=> (&& (<= ?b ?a) (< ?b ?a))
(< ?b ?a) <=> (&& (< ?b ?a) (!= ?b ?a))
(< ?b ?a) <=> (&& (!= ?b ?a) (<= ?b ?a))
(&& (!= ?b ?a) (!= ?b ?a)) <=> (!= ?b ?a)
(&& (< ?a ?b) (< ?b ?a)) ==> 0
(&& (<= ?a ?b) (< ?b ?a)) ==> 0
(&& (== ?b ?a) 1) <=> (== ?b ?a)
(&& (<= ?b ?a) 1) <=> (<= ?b ?a)
(&& (<= ?b ?a) (!= ?b ?c)) <=> (&& (!= ?b ?c) (<= ?b ?a))
(&& (< ?b ?a) (<= ?a ?c)) <=> (&& (<= ?a ?c) (< ?b ?a))
(&& (<= ?b ?a) (< ?c ?a)) <=> (&& (< ?c ?a) (<= ?b ?a))
(&& (!= ?b ?a) (< ?c ?a)) <=> (&& (< ?c ?a) (!= ?b ?a))
(&& (<= ?b ?a) (< ?a ?c)) <=> (&& (< ?a ?c) (<= ?b ?a))
(&& (< ?b ?a) (!= ?b ?c)) <=> (&& (!= ?b ?c) (< ?b ?a))
(&& (< ?b ?a) (< ?c ?a)) <=> (&& (< ?c ?a) (< ?b ?a))
(&& (<= ?b ?a) (<= ?b ?c)) <=> (&& (<= ?b ?c) (<= ?b ?a))
(&& (<= ?b ?a) (<= ?c ?b)) <=> (&& (<= ?c ?b) (<= ?b ?a))
(&& (< ?b ?a) (< ?a ?c)) <=> (&& (< ?a ?c) (< ?b ?a))
(&& (<= ?b ?c) (== ?c ?a)) <=> (&& (== ?c ?a) (<= ?b ?a))
(&& (<= ?b ?a) (<= ?c ?a)) <=> (&& (<= ?c ?a) (<= ?b ?a))
(&& (!= ?b ?a) (!= ?b ?c)) <=> (&& (!= ?b ?c) (!= ?b ?a))
(&& (< ?b ?a) (< ?b ?c)) <=> (&& (< ?b ?c) (< ?b ?a))
(&& (< ?b ?a) (<= ?b ?c)) <=> (&& (<= ?b ?c) (< ?b ?a))
(&& (== ?b ?a) (< ?b ?c)) <=> (&& (< ?a ?c) (== ?b ?a))
(&& (== ?b ?a) (< ?a ?c)) <=> (&& (< ?a ?c) (== ?b ?a))
(&& (!= ?b ?a) (<= ?c ?a)) <=> (&& (<= ?c ?a) (!= ?b ?a))
(&& (== ?b ?a) (<= ?a ?c)) <=> (&& (<= ?b ?c) (== ?b ?a))
(&& (!= ?c ?b) (== ?b ?a)) <=> (&& (!= ?c ?a) (== ?b ?a))
(&& (!= ?b ?c) (== ?c ?a)) <=> (&& (== ?c ?a) (!= ?b ?a))
(&& (== ?b ?a) (<= ?b ?c)) <=> (&& (<= ?b ?c) (== ?b ?a))
(&& (< ?b ?c) (== ?a ?c)) <=> (&& (== ?a ?c) (< ?b ?a))
(&& (== ?c ?a) (< ?b ?c)) <=> (&& (== ?c ?a) (< ?b ?a))
(&& (== ?b ?a) (== ?b ?c)) <=> (&& (== ?c ?a) (== ?b ?a))
(&& (== ?b ?a) (== ?b ?c)) <=> (&& (== ?b ?c) (== ?b ?a))
(&& (== ?c ?a) (<= ?b ?c)) <=> (&& (== ?c ?a) (<= ?b ?a))
(&& 0 (<= ?b ?a)) ==> 0
(&& 0 (!= ?b ?a)) ==> 0
(&& (== ?b ?a) 0) ==> 0
(&& (< ?b ?a) 0) ==> 0
(&& (!= ?b ?a) 0) ==> 0
(&& 0 (< ?b ?a)) ==> 0
(&& (<= ?b ?a) 0) ==> 0
(!= ?b ?a) <=> (&& 1 (!= ?b ?a))
(!= ?b ?a) <=> (&& (!= ?b ?a) 1)
(< ?b ?a) <=> (&& (< ?b ?a) 1)
(< ?b ?a) <=> (&& 1 (< ?b ?a))
(<= ?b ?a) <=> (&& 1 (<= ?b ?a))
(&& (<= ?b ?c) (!= ?a ?b)) <=> (&& (<= ?b ?c) (< ?b ?a)) if  (<= ?c ?a)
(&& (<= ?c ?b) (== ?b ?a)) <=> (&& (<= ?c ?b) (<= ?b ?a)) if  (<= ?a ?c)
(&& (<= ?b ?c) (== ?b ?a)) <=> (&& (<= ?b ?c) (<= ?a ?b)) if  (<= ?c ?a)
(&& (<= ?c ?a) (!= ?b ?a)) <=> (&& (<= ?c ?a) (< ?b ?a)) if  (<= ?b ?c)
(&& (<= ?b ?a) (< ?c ?a)) ==> (<= ?b ?a) if (< ?c ?b)
(&& (<= ?b ?a) (< ?b ?c)) ==> (<= ?b ?a) if (< ?a ?c)
(&& (<= ?a ?c) (!= ?b ?a)) ==> (<= ?a ?c) if (< ?c ?b)
(&& (<= ?b ?a) (!= ?c ?a)) ==> (<= ?b ?a) if (< ?c ?b)
(&& (<= ?b ?c) (< ?b ?a)) ==> (< ?b ?a) if (<= ?a ?c)
(&& (<= ?c ?a) (< ?b ?a)) ==> (< ?b ?a) if (<= ?c ?b)
(&& (<= ?c ?a) (<= ?b ?a)) ==> (<= ?c ?a) if (<= ?b ?c)
(&& (<= ?b ?c) (<= ?b ?a)) ==> (<= ?b ?a) if (<= ?a ?c)
(&& (< ?c ?a) (< ?b ?a)) ==> (< ?b ?a) if (<= ?c ?b)
(&& (< ?b ?a) (!= ?b ?c)) ==> (< ?b ?a) if (<= ?a ?c)
(&& (< ?b ?a) (!= ?c ?a)) ==> (< ?b ?a) if (<= ?c ?b)
(&& (< ?b ?c) (< ?b ?a)) ==> (< ?b ?a) if (<= ?a ?c)
(&& (<= ?a ?c) (<= ?b ?a)) ==> 0 if (< ?c ?b)
(&& (<= ?a ?c) (< ?b ?a)) ==> 0 if (<= ?c ?b)
(&& (<= ?c ?b) (< ?b ?a)) ==> 0 if (<= ?a ?c)
(&& (< ?a ?c) (< ?b ?a)) ==> 0 if (<= ?c ?b)
(< ?a ?b) <=> (> ?b ?a)
(+ ?a ?b) <=> (+ ?b ?a)
(> ?a ?a) ==> 0
(- ?a ?a) ==> 0
(+ 0 ?a) <=> ?a
(- ?a 0) <=> ?a
(< ?a 1) <=> (< ?a 0) if  (!= ?a 0)
(< 1 ?a) ==> 0 if (<= ?a 0)
(< ?a 1) ==> 1 if (<= ?a 0)
(< ?a 1) ==> 0 if (< 0 ?a)
(< ?a (< 0 1)) <=> (< ?a (- 1 ?a))
(< ?a (< ?a 1)) <=> (< ?a (- 1 ?a))
(- ?a (- ?a 1)) ==> (< 0 1)
(< (- ?a 1) ?a) ==> 1
(- 1 (< ?b ?a)) <=> (< (- ?a 1) ?b)
(< (< ?b ?a) ?a) <=> (< (< ?b 1) ?a)
(< (< ?a ?b) ?a) <=> (< (< 1 ?b) ?a)
(< (+ ?b ?a) ?a) ==> (< ?b (< 0 ?b))
(< (+ ?a ?b) ?b) ==> (< (+ ?a ?a) 0)
(< ?a (+ ?b ?a)) ==> (< (< ?b 1) ?b)
(< ?a (+ ?b ?a)) ==> (< (- 0 ?b) ?b)
(< ?a (+ ?b ?a)) ==> (< (< 1 ?b) ?b)
(- (+ ?c ?a) ?b) <=> (- ?c (- ?b ?a))
(< (- ?c ?a) ?b) <=> (< ?c (+ ?b ?a))
(- (- ?c ?a) ?b) <=> (- ?c (+ ?b ?a))
(< (+ ?c ?a) ?b) <=> (< ?c (- ?b ?a))
(+ ?a (+ ?c ?b)) <=> (+ ?c (+ ?b ?a))
(< (< ?b ?a) 0) ==> 0
(< 1 (< ?b ?a)) ==> 0
(< ?b ?a) <=> (< 0 (< ?b ?a))
(< ?a (< ?b 0)) <=> (< ?a (< ?b ?a))
(< (- ?a ?b) ?a) ==> (< (< ?b 0) ?b)
(< ?a (+ ?b ?a)) ==> (< (- 1 ?b) ?b)
(- 0 (< ?a ?b)) <=> (- (< ?b ?a) 1) if  (!= ?b ?a)
(- (< ?b ?a) 1) <=> (- 0 (< ?a ?b)) if  (!= ?a ?b)
(< (< ?a ?b) ?a) <=> (< (< 0 ?b) ?a) if  (!= ?b ?a)
(< ?a (< ?b 1)) <=> (< ?a (< ?b ?a)) if  (!= ?b ?a)
(< ?b (< ?a ?b)) <=> (< ?b (< ?a 1)) if  (!= ?b ?a)
(< (< 0 ?b) ?a) <=> (< (< ?a ?b) ?a) if  (!= ?a ?b)
(< (< ?b ?a) 1) <=> (< ?a ?b) if  (!= ?a ?b)
(< (- ?b ?a) 1) <=> (< ?b ?a) if  (!= ?a ?b)
(< ?c (< ?b ?a)) ==> (< ?c 0) if (!= ?c 0)
(< ?c (< ?b ?a)) ==> 1 if (< ?c 0)
(< (< ?c ?b) ?a) ==> 0 if (<= ?a 0)
(< ?c (< ?b ?a)) ==> 0 if (< 0 ?c)
(* ?a ?b) <=> (* ?b ?a)
(- (- ?a)) <=> ?a
(/ ?a 1) <=> ?a
(* ?a 1) <=> ?a
(- ?a) <=> (- 0 ?a)
(* ?a 0) ==> 0
(/ 0 ?a) ==> 0
(/ ?a 0) ==> 0
(/ ?a ?a) ==> 1 if (!= ?a 0)
(/ ?b (- ?a)) <=> (- (/ ?b ?a))
(/ (- ?b) ?a) <=> (- (/ ?b ?a))
(- (* ?b ?a)) <=> (* ?a (- ?b))
(- ?b ?a) <=> (- (- ?a ?b))
(+ ?b ?a) <=> (- ?a (- ?b))
(/ 1 (* ?a ?a)) <=> (/ ?a (/ 1 ?a))
(/ 1 ?a) <=> (/ (/ ?a ?a) ?a)
(/ 1 (+ ?a ?a)) ==> 0
(/ ?a (+ ?a ?a)) ==> 0
(* ?b (/ 1 ?a)) <=> (/ ?b (/ 1 ?a))
(+ ?b (* ?b ?a)) <=> (* ?b (+ ?a 1))
(- (* ?b ?a) ?a) <=> (* ?a (- ?b 1))
(* ?b (+ ?a ?a)) <=> (* ?a (+ ?b ?b))
(+ ?b (- ?a ?b)) ==> (* ?a (/ ?a ?a))
(/ (* ?a ?b) ?a) <=> (* ?b (/ ?a ?a))
(/ (* ?a ?b) ?a) <=> (/ ?b (/ ?a ?a))
(+ ?c (- ?b ?a)) <=> (- (+ ?b ?c) ?a)
(/ ?c (* ?b ?a)) <=> (/ (/ ?c ?a) ?b)
(* ?c (* ?b ?a)) <=> (* ?b (* ?c ?a))
(- (- ?c ?b) ?a) <=> (- ?c (+ ?a ?b))
(/ (- 1 ?a) ?a) <=> (- (/ 1 ?a) 1) if  (< ?a 0)
(/ 1 (- ?a 1)) <=> (- (/ ?a ?a) 1) if  (<= ?a 0)
(+ 1 (/ 1 ?a)) <=> (/ (+ ?a 1) ?a) if  (< 0 ?a)
(/ 1 (* ?a ?a)) <=> (- (/ 1 ?a)) if  (<= ?a 0)
(* ?a (/ 1 ?a)) <=> (/ 1 ?a) if  (<= 0 ?a)
(/ 1 (- ?a 1)) ==> 0 if (< ?a 0)
(/ 1 (+ ?a 1)) ==> 0 if (< 0 ?a)
(/ (+ ?a 1) ?a) ==> 0 if (<= ?a 0)
(/ ?a (- 1 ?a)) ==> 0 if (<= ?a 0)
(/ ?a (+ ?a 1)) ==> 0 if (<= 0 ?a)
(/ (- 1 ?a) ?a) ==> 0 if (<= 0 ?a)
(min ?a ?b) <=> (min ?b ?a)
(max ?a ?b) <=> (max ?b ?a)
(max ?a ?a) <=> ?a
(min ?a ?a) <=> ?a
(/ ?a ?a) ==> 1 if (< 0 ?a)
(max ?a (* ?a ?a)) <=> (* ?a ?a)
(min ?a (max ?b ?a)) ==> (min ?a (* ?a ?a))
(min ?a (max ?b ?a)) ==> (/ (* ?a ?a) ?a)
(max ?b (min ?b ?a)) ==> ?b
(min ?b (max ?b ?a)) ==> ?b
(max ?c (max ?b ?a)) <=> (max ?a (max ?c ?b))
(/ ?c (* ?a ?b)) <=> (/ (/ ?c ?b) ?a)
(min ?b (min ?c ?a)) <=> (min ?c (min ?b ?a))
(/ (min ?b ?a) ?b) <=> (/ ?a (max ?b ?a)) if  (< 0 ?b)
(/ ?a (min ?b ?a)) <=> (/ (max ?b ?a) ?b) if  (< 0 ?a)
(max ?b (/ ?a ?a)) ==> (max ?b 1) if (< 0 ?b)
(max ?b (/ ?b ?a)) ==> (max ?b 1) if (< 0 ?b)
(max ?b (/ ?b ?a)) ==> ?b if (< 0 ?b)
(max ?b (/ ?a ?a)) ==> ?b if (< 0 ?b)
(/ ?b (/ ?b ?a)) <=> (* ?a (/ ?b ?b)) if  (== ("%" ?b ?a) 0)
(/ (* ?b ?b) ?a) <=> (/ ?b (/ ?a ?b)) if  (== ("%" ?a ?b) 0)
(* ?c (/ ?b ?a)) <=> (/ (* ?b ?c) ?a) if  (== ("%" ?b ?a) 0)
(* ?c (/ ?b ?a)) <=> (/ ?c (/ ?b ?a)) if  (== ("%" ?a ?b) 0)
(min ?a ?b) ==> ?a if (<= ?a ?b)
(max ?b ?a) ==> ?b if (<= ?a ?b)
(max ?c (min ?b ?a)) <=> (min ?a (max ?c ?b)) if  (<= ?c ?a)
(min ?c (max ?b ?a)) <=> (max (min ?a ?c) (min ?b ?c))
(min (max ?b ?c) (max ?b ?a)) <=> (max ?b (min ?a ?c))
(max ?b (min ?c (max ?b ?a))) <=> (max ?b (min ?a ?c))
(min ?a 1) ==> 1 if (< 0 ?a)
?a <=> (min ?a 1) if  (<= ?a 0)
?a <=> (min ?a (+ ?a 1))
(max ?a (+ ?b ?a)) <=> (+ ?a (max ?b 0))
(min ?a (+ ?b ?a)) <=> (+ ?a (min ?b 0))
(+ ?a (max ?a 1)) <=> (max (+ ?a ?a) 1) if  (<= 0 ?a)
(min (+ ?a ?a) 1) <=> (min ?a 1) if  (<= 0 ?a)
(min ?b (+ ?a 1)) ==> (+ ?a 1) if (< ?a ?b)
(max ?b (+ ?a 1)) ==> ?b if (< ?a ?b)
(== 1 (min ?b ?a)) ==> 0 if (<= ?b 0)
(== (min ?b ?c) (min ?b ?a)) ==> (== (min ?b ?c) ?b) if (< ?c ?a)
(== ?c (min ?b ?a)) ==> (== ?c ?b) if (< ?c ?a)
(== (min ?c ?b) ?a) ==> 0 if (< ?b ?a)
(== 1 ?a) ==> 0 if (<= ?a 0)
(== 1 (max ?b ?a)) ==> (== 1 ?a) if (<= ?b 0)
(== (max ?c ?a) (max ?b ?a)) ==> (== ?a (max ?c ?a)) if (< ?b ?c)
(== ?b (max ?a ?c)) ==> (== ?b ?a) if (< ?c ?b)
(== (max ?c ?b) ?a) ==> 0 if (< ?a ?b)
(max ?b (* ?a ?a)) ==> (* ?a ?a) if (<= ?b 0)
(min ?b (* ?a ?a)) ==> ?b if (<= ?b 0)
(min ?b (* ?a (max ?b ?a))) <=> (min ?b (* ?b (min ?b ?a)))
(* (min ?b ?a) (max ?b ?a)) <=> (* ?b ?a)
(* ?a (* ?a ?a)) <=> (max ?a (* ?a (* ?a ?a))) if  (<= 0 ?a)
(min ?b (max ?a (* ?b ?a))) ==> (max ?b (* ?b (* ?b ?b))) if (<= ?b 0)
(min ?a (* ?a (min ?b ?a))) <=> (min ?a (max ?b (* ?b ?a))) if  (<= 0 ?b)
(min ?a (max ?b (* ?a ?b))) <=> (min ?a (* ?b (* ?a ?a))) if  (<= 0 ?b)
(min ?a (* ?b (* ?a ?a))) <=> (* ?b (* ?a ?a)) if  (< ?b 0)
(* ?a (max ?b ?a)) <=> (max ?a (* ?a (max ?b ?a))) if  (<= ?b 0)
(max ?a (* ?b (max ?b ?a))) <=> (* ?b (max ?b ?a)) if  (<= ?a 0)
(min ?b (* ?b ?a)) <=> (min ?b (* ?a (min ?b ?a))) if  (<= ?b 0)
(min ?b (* ?a (min ?b ?a))) <=> (min ?b (* ?a ?a)) if  (<= ?a 0)
(min ?b (* ?b (min ?b ?a))) <=> (min ?b (* ?b ?a)) if  (<= ?a 0)
(* ?b (max ?b ?a)) <=> (max ?a (* ?b (max ?b ?a))) if  (< 0 ?b)
(max ?a (* ?a (min ?b ?a))) <=> (* ?a (min ?b ?a)) if  (< 0 ?b)
(min ?a (* ?b ?a)) <=> (min ?a (* ?a (max ?b ?a))) if  (< 0 ?b)
(* ?b (* ?a ?a)) <=> (max ?a (* ?b (* ?a ?a))) if  (< 0 ?b)
(min ?b (* ?a (min ?b ?a))) <=> (min ?b (* ?a ?a)) if  (<= 0 ?b)
(max ?a (* ?a (* ?a ?b))) ==> ?a if (< ?b 0)
(min ?a (max ?b (* ?a ?b))) ==> ?a if (<= ?a 0)
(min ?a (* ?a (max ?b ?a))) ==> ?a if (<= ?b 0)
(min ?a (* ?a (* ?a ?b))) ==> ?a if (< 0 ?b)
(min ?b (max ?a (* ?b ?a))) ==> ?b if (< 0 ?a)
(min ?a (* ?a (min ?a ?b))) ==> ?a if (< 0 ?b)
(min ?a (* ?a (max ?b ?a))) ==> ?a if (<= 0 ?a)
(min ?c (* ?b (max ?b ?a))) <=> (min ?c (* ?a (min ?b ?a))) if  (<= ?c 0)
(min (* ?c ?b) (* ?c ?a)) <=> (* ?c (max ?b ?a)) if  (<= ?c 0)
(max (* ?c ?b) (* ?b ?a)) <=> (* ?b (min ?c ?a)) if  (<= ?b 0)
(* ?a (max ?c ?b)) <=> (max (* ?c ?a) (* ?b ?a)) if  (<= 0 ?a)
(min (* ?c ?b) (* ?b ?a)) <=> (* ?b (min ?c ?a)) if  (<= 0 ?b)
(< (min ?b ?a) (+ ?b (+ ?a ?a))) <=> (< (min ?b (+ ?b ?b)) (+ ?a (+ ?b ?b)))
(< (+ ?a (+ ?b ?b)) (min ?b ?a)) <=> (< (+ ?b (+ ?a ?a)) (min ?a (+ ?a ?a)))
(< (+ ?b ?b) (min ?b (+ ?a ?a))) <=> (< (+ ?b ?a) (min ?a (+ ?a ?a)))
(< (min ?b (+ ?b ?b)) (+ ?b (+ ?a ?a))) <=> (< (min ?b ?a) (+ ?a ?a))
(< (min ?a (+ ?b ?b)) (+ ?a ?a)) <=> (< (min ?b (+ ?b ?b)) (+ ?b ?a))
(< ?b ?a) <=> (< (min ?b (+ ?b ?b)) (min ?a (+ ?a ?a)))
(< ?b ?a) <=> (< (+ ?b (+ ?b ?b)) (+ ?a (+ ?a ?a)))
(< (+ ?c (+ ?b ?b)) (+ ?c (min ?b ?a))) <=> (< (+ ?c (+ ?b ?b)) (min ?c (+ ?c ?a)))
(< (+ ?b (min ?c ?a)) (+ ?b (+ ?a ?a))) <=> (< (min ?b (+ ?b ?c)) (+ ?b (+ ?a ?a)))
(< (+ ?a (min ?b ?a)) (min ?c (+ ?b ?a))) <=> (< (+ ?a (min ?b ?a)) (min ?c (+ ?b ?b)))
(< (+ ?b (min ?c ?a)) (+ ?b (+ ?b ?a))) <=> (< (min ?a (+ ?b ?c)) (+ ?b (+ ?b ?a)))
(< (min ?c ?b) (+ ?b (+ ?a ?a))) <=> (< (min ?c (+ ?b ?a)) (+ ?b (+ ?a ?a)))
(< (+ ?c (min ?c ?b)) (+ ?b (min ?b ?a))) <=> (< (+ ?c ?c) (+ ?b (min ?c ?a)))
(< (+ ?b (min ?a ?c)) (+ ?b ?a)) <=> (< (+ ?b (+ ?a ?c)) (+ ?b (+ ?a ?a)))
(< (+ ?c (min ?c ?a)) (min ?b (+ ?a ?a))) <=> (< (+ ?c ?c) (min ?b (+ ?a ?a)))
(< (+ ?b (+ ?a ?a)) (min ?c (+ ?b ?a))) <=> (< (+ ?b (+ ?a ?a)) (min ?b ?c))
(< (min ?c (+ ?b ?b)) (+ ?a (min ?b ?a))) <=> (< (min ?c (+ ?b ?b)) (+ ?a ?a))
(< (+ ?b (min ?c ?b)) (+ ?a ?a)) <=> (< (+ ?b (min ?c ?b)) (+ ?a (min ?b ?a)))
(< (+ ?b ?c) (+ ?b ?a)) <=> (< (+ ?b (+ ?c ?c)) (+ ?b (+ ?a ?a)))
(< (+ ?c (+ ?b ?b)) (min ?c (+ ?b ?a))) <=> (< (+ ?b ?c) (min ?c ?a))
(< (min ?b (+ ?c ?a)) (+ ?b (+ ?a ?a))) <=> (< (min ?b ?c) (+ ?b ?a))
(< (+ ?b ?b) (min ?c (+ ?b ?a))) <=> (< (+ ?b ?b) (min ?c (+ ?a ?a)))
(< (+ ?c ?b) (+ ?b ?a)) <=> (< (+ ?c (min ?c ?b)) (+ ?a (min ?b ?a)))
(< (+ ?c (min ?c ?b)) (+ ?a ?a)) <=> (< (+ ?c (min ?b ?a)) (+ ?a ?a))
(< (min ?c (+ ?b ?a)) (+ ?a ?a)) <=> (< (min ?c (+ ?b ?b)) (+ ?a ?a))
(< (+ ?c ?c) (+ ?a (min ?b ?a))) <=> (< (+ ?c ?c) (+ ?a (min ?c ?b)))
(< (+ ?c ?b) (+ ?c (min ?b ?a))) ==> 0
(< ?c (min ?c (min ?b ?a))) ==> 0
(< (+ ?b ?d) (min ?c (+ ?b ?a))) <=> (< (+ ?b (min ?d ?a)) (min ?c (+ ?b ?a)))
(< (min ?b (+ ?d ?c)) (min ?b ?a)) <=> (< (+ ?b (+ ?d ?c)) (+ ?b (min ?b ?a)))
(< (+ ?b (min ?d ?c)) (+ ?c (min ?b ?a))) <=> (< (+ ?b ?d) (+ ?c (min ?b ?a)))
(< (+ ?c ?d) (+ ?c (min ?b ?a))) <=> (< (+ ?c (min ?d ?b)) (+ ?c (min ?b ?a)))
(< (min ?d (+ ?c ?b)) (+ ?c (min ?b ?a))) <=> (< ?d (+ ?c (min ?b ?a)))
(< (+ ?d ?c) (min ?b ?a)) <=> (< (min ?b (+ ?d ?c)) (min ?b ?a))
(< (min ?a (+ ?b ?b)) (+ ?a (+ ?a ?a))) <=> (< (+ ?b (min ?a ?b)) (+ ?a (+ ?a ?a))) if  (< ?b 0)
(< (min ?a (+ ?b ?b)) (+ ?a (+ ?a ?a))) <=> (< (+ ?b (min ?b ?a)) (+ ?a (+ ?a ?a))) if  (< ?a 0)
(< (+ ?b (+ ?b ?b)) (+ ?a (min ?b ?a))) <=> (< (+ ?b (+ ?b ?b)) (+ ?a ?a)) if  (< ?a 0)
(< (+ ?b (+ ?b ?b)) (min ?a (+ ?b ?a))) <=> (< (+ ?b ?b) ?a) if  (< ?a 0)
(< (+ ?a (+ ?b ?b)) (min ?b (+ ?a ?a))) <=> (< (+ ?b ?b) ?a) if  (< ?a 0)
(< (+ ?a (min ?b ?a)) ?b) <=> (< (+ ?b (+ ?a ?a)) (min ?b ?a)) if  (< ?b 0)
(< ?b (+ ?a ?a)) <=> (< (min ?b (+ ?b ?a)) (+ ?a (+ ?a ?a))) if  (< ?b 0)
(< (min ?b (+ ?a ?b)) (+ ?a ?a)) <=> (< (min ?a ?b) ?a) if  (< ?b 0)
(< (+ ?b ?a) (min ?b ?a)) <=> (< (+ ?a (min ?b ?a)) ?b) if  (< ?b 0)
(< (min ?b ?a) (+ ?b ?a)) ==> (< ?b (+ ?b ?b)) if (< ?a 0)
(min ?a (+ ?a ?b)) ==> ?a if (< 0 ?b)
(< (min ?b (min ?a ?c)) (+ ?b (min ?a ?c))) ==> (< (min ?a (+ ?b ?b)) (+ ?b (min ?b ?a))) if (< ?a 0)
(< (+ ?c (min ?b ?a)) (min ?a (+ ?a ?a))) <=> (< (+ ?c (min ?c ?b)) (min ?a (+ ?a ?a))) if  (< ?b 0)
(< (min ?b (+ ?b ?b)) (+ ?c (min ?a ?c))) <=> (< (min ?b (+ ?b ?b)) (+ ?c (min ?b ?a))) if  (< ?a 0)
(< (min ?b (+ ?c ?c)) (+ ?c (min ?b ?a))) <=> (< (min ?b (+ ?b ?c)) (+ ?b (min ?b ?a))) if  (< ?c 0)
(< (+ ?c (min ?b ?a)) (min ?b (+ ?a ?a))) <=> (< (+ ?c (min ?c ?b)) (min ?b (+ ?a ?a))) if  (< ?b 0)
(< (min ?b (+ ?c ?c)) (+ ?a (min ?b ?a))) <=> (< (min ?b (+ ?c ?c)) (+ ?a (min ?c ?b))) if  (< ?b 0)
(< (min ?b (+ ?a ?a)) (min ?c (+ ?b ?b))) <=> (< (+ ?a (min ?b ?a)) (min ?c (+ ?b ?a))) if  (< ?b 0)
(< (min ?b (+ ?c ?c)) (+ ?a (min ?b ?c))) <=> (< (min ?b (+ ?c ?c)) (+ ?a (min ?b ?a))) if  (< ?c 0)
(< (min ?c (+ ?c ?b)) (+ ?b (min ?b ?a))) <=> (< (min ?c (+ ?c ?c)) (+ ?b (min ?b ?a))) if  (< 0 ?a)
(< (min ?b (min ?a ?c)) (+ ?a (min ?b ?a))) <=> (< (+ ?b (min ?a ?c)) (+ ?b (+ ?a ?a))) if  (< 0 ?c)
(< (+ ?b (min ?a ?c)) (min ?a (+ ?b ?a))) <=> (< (+ ?c (min ?b ?a)) (min ?a (+ ?b ?a))) if  (< 0 ?c)
(< (min ?c (+ ?c ?c)) (min ?b (+ ?a ?a))) <=> (< (min ?c (+ ?c ?a)) (min ?b (+ ?a ?a))) if  (< 0 ?b)
(< (min ?b ?c) (+ ?b (+ ?a ?a))) <=> (< (min ?b (min ?c ?a)) (+ ?b (+ ?a ?a))) if  (< ?b 0)
(< (min ?c ?b) (+ ?a (+ ?a ?a))) <=> (< (min ?c (min ?b ?a)) (+ ?a (+ ?a ?a))) if  (< ?b 0)
(< (min ?c (+ ?b ?b)) (+ ?c (min ?c ?a))) <=> (< (+ ?b ?b) (+ ?c (min ?b ?a))) if  (< ?b 0)
(< (+ ?b (min ?c ?b)) (min ?a (+ ?a ?a))) <=> (< (+ ?b (min ?c ?b)) (+ ?a ?a)) if  (< ?b 0)
(< (+ ?b (+ ?c ?c)) (min ?b ?a)) <=> (< (+ ?b (+ ?c ?c)) (min ?c (min ?b ?a))) if  (< ?b 0)
(< (min ?a (min ?b ?c)) (+ ?a (min ?b ?c))) ==> (< (min ?a ?b) (+ ?b (+ ?a ?a))) if (< ?b 0)
(< (min ?a (+ ?b ?c)) (+ ?b (min ?b ?a))) <=> (< (min ?b (min ?c ?a)) (min ?b ?a)) if  (< ?b 0)
(< (+ ?c (+ ?b ?b)) (+ ?a ?a)) <=> (< (+ ?c (+ ?b ?b)) (+ ?a (min ?b ?a))) if  (< ?c 0)
(< (+ ?c (+ ?c ?c)) (min ?b ?a)) <=> (< (+ ?c (+ ?c ?c)) (min ?c (min ?b ?a))) if  (< ?b 0)
(< (+ ?b ?b) (+ ?c (min ?b ?a))) <=> (< (min ?b (+ ?b ?b)) (+ ?c (min ?c ?a))) if  (< ?c 0)
(< (min ?a (+ ?b ?b)) (min ?c (+ ?a ?a))) <=> (< (+ ?b ?b) (min ?c (+ ?b ?a))) if  (< ?b 0)
(< (min ?b ?a) (+ ?c (min ?b ?a))) <=> (< (+ ?b (min ?a ?c)) (+ ?b (+ ?a ?c))) if  (< ?a 0)
(< (min ?b (+ ?b ?a)) (min ?c (+ ?b ?a))) <=> (< (min ?b ?a) (min ?c (+ ?b ?a))) if  (< ?b 0)
(< (min ?c (min ?b ?a)) (+ ?a (+ ?a ?a))) <=> (< (min ?c ?b) (+ ?a (+ ?a ?a))) if  (< ?c 0)
(< (+ ?a (min ?c ?b)) (min ?c (min ?b ?a))) <=> (< (+ ?c (+ ?b ?a)) (+ ?c ?b)) if  (< ?b 0)
(< (min ?c (min ?b ?a)) (+ ?c (min ?b ?a))) ==> (< (min ?c ?b) (min ?c (+ ?c ?b))) if (< ?b 0)
(< (+ ?c (min ?b ?a)) (min ?c (+ ?b ?a))) <=> (< (+ ?c (min ?b ?a)) (+ ?b ?a)) if  (< ?b 0)
(< (+ ?b (+ ?b ?b)) (min ?b (min ?a ?c))) ==> (< (+ ?b (+ ?b ?b)) (min ?b ?a)) if (< 0 ?c)
(< (min ?c (min ?b ?a)) (+ ?c (+ ?b ?a))) <=> (< (min ?c ?b) (+ ?c (+ ?b ?a))) if  (< 0 ?a)
(< (min ?a (min ?b ?c)) (+ ?b (+ ?a ?a))) ==> (< (min ?a ?b) (+ ?b (+ ?a ?a))) if (< 0 ?c)
(< (+ ?b ?c) (+ ?b (+ ?b ?a))) <=> (< (+ ?c (min ?b ?c)) (+ ?b (+ ?b ?a))) if  (< 0 ?a)
(< (min ?b ?c) (+ ?b (+ ?b ?a))) <=> (< (min ?b (min ?c ?a)) (+ ?b (+ ?b ?a))) if  (< 0 ?a)
(< (+ ?a ?c) (min ?b (+ ?a ?a))) <=> (< (+ ?a (min ?c ?b)) (min ?b (+ ?a ?a))) if  (< 0 ?b)
(< (min ?a (min ?b ?c)) (+ ?a (+ ?a ?a))) ==> (< (min ?a ?b) (+ ?a (+ ?a ?a))) if (< 0 ?c)
(< (+ ?b (min ?a ?c)) (min ?b (+ ?a ?a))) ==> (< (+ ?b ?a) (min ?b (+ ?a ?a))) if (< 0 ?c)
(< (+ ?b (+ ?a ?c)) (min ?b ?a)) <=> (< (+ ?b (+ ?a ?c)) (min ?b (min ?a ?c))) if  (< 0 ?c)
(< (+ ?b (+ ?c ?c)) (min ?c (min ?b ?a))) ==> (< (+ ?b (+ ?c ?c)) (min ?c ?b)) if (< 0 ?a)
(< (+ ?a (min ?b ?c)) (min ?a (+ ?a ?a))) ==> (< (+ ?a ?b) (min ?a (+ ?a ?a))) if (< 0 ?c)
(< ?a (+ ?a (min ?b ?c))) ==> (< (min ?a (+ ?a ?a)) (min ?b (+ ?a ?a))) if (< ?b 0)
(< (min ?a (+ ?b ?a)) (min ?c (+ ?b ?a))) ==> (< ?b (min ?b (+ ?a ?a))) if (< ?b 0)
(< (min ?a (+ ?b ?a)) (+ ?b (min ?a ?c))) ==> (< ?b (min ?b (+ ?a ?a))) if (< ?b 0)
(< ?c (min ?b (+ ?a ?a))) <=> (< (min ?c (min ?b ?a)) (min ?b (+ ?a ?a))) if  (< ?b 0)
(< (min ?c (min ?b ?a)) (min ?b (+ ?b ?a))) <=> (< ?c (min ?b (+ ?b ?a))) if  (< ?b 0)
(< (min ?b (+ ?b ?c)) (+ ?b (min ?b ?a))) <=> (< (min ?b ?c) (min ?b ?a)) if  (< ?b 0)
(< (min ?c (+ ?b ?a)) (+ ?a (min ?b ?c))) ==> (< ?b (+ ?b (min ?b ?a))) if (< ?a 0)
(< (min ?c (min ?b ?a)) ?a) <=> (< (+ ?c (min ?c ?b)) (min ?c (+ ?c ?a))) if  (< ?b 0)
(< ?b (min ?c (+ ?b ?a))) <=> (< (min ?b (min ?a ?c)) (min ?c (+ ?b ?a))) if  (< ?b 0)
(< (min ?b (min ?a ?c)) (+ ?a (min ?b ?c))) ==> (< ?b (min ?a (+ ?b ?a))) if (< ?b 0)
(< ?c (+ ?b (+ ?b ?a))) <=> (< (min ?c (+ ?b ?a)) (+ ?b (+ ?b ?a))) if  (< ?b 0)
(< (min ?b ?c) (min ?b ?a)) <=> (< (min ?a (+ ?b ?c)) (+ ?b (min ?b ?a))) if  (< ?b 0)
(< (min ?a (+ ?b ?a)) (+ ?a (min ?b ?c))) ==> (< ?b (min ?b (+ ?a ?a))) if (< ?b 0)
(< ?c (min ?c (+ ?b ?a))) ==> (< (min ?c (+ ?c ?c)) (min ?b (+ ?c ?c))) if (< ?b 0)
(< (min ?b (+ ?a ?c)) (min ?a (+ ?b ?a))) ==> (< ?b (min ?a (+ ?b ?a))) if (< 0 ?c)
(< (min ?a (+ ?b ?c)) (min ?b (+ ?a ?a))) ==> (< ?a (min ?b (+ ?a ?a))) if (< 0 ?c)
(< (+ ?b (min ?a ?c)) (min ?c (+ ?a ?b))) ==> (< ?a (min ?a (+ ?a ?a))) if (< 0 ?b)
(< (min ?b (+ ?a ?c)) (min ?a (+ ?a ?a))) ==> (< ?b (min ?a (+ ?a ?a))) if (< 0 ?c)
(< (min ?c (+ ?a ?b)) (min ?b (+ ?a ?a))) <=> (< ?c (min ?b (+ ?a ?a))) if  (< 0 ?b)
(< (min ?c (+ ?b ?b)) (min ?a (+ ?b ?a))) <=> (< (min ?c (+ ?b ?b)) ?a) if  (< 0 ?a)
(< (+ ?b (min ?c ?b)) ?a) <=> (< (+ ?b (min ?c ?b)) (min ?a (+ ?b ?a))) if  (< 0 ?a)
(< ?b (+ ?c (min ?b ?a))) <=> (< (min ?b ?c) (+ ?c (min ?b ?a))) if  (< ?b 0)
(< ?c (min ?c (+ ?b ?a))) ==> (< (min ?c ?b) (min ?b (+ ?c ?b))) if (< ?b 0)
(< (min ?c (+ ?b ?a)) (min ?a (+ ?b ?a))) <=> (< ?c (+ ?b ?a)) if  (< ?b 0)
(< ?a (+ ?a (min ?b ?c))) ==> (< (min ?a ?b) (min ?b (+ ?a ?a))) if (< ?b 0)
(< (min ?c ?b) (+ ?a ?a)) <=> (< (min ?c (min ?b ?a)) (+ ?a ?a)) if  (< ?b 0)
(< (min ?b ?a) (min ?c (+ ?b ?a))) <=> (< ?b (min ?c (+ ?b ?a))) if  (< ?b 0)
(< (min ?a (+ ?c ?b)) (+ ?b (+ ?b ?a))) <=> (< ?c (+ ?b ?a)) if  (< ?b 0)
(< (+ ?a (min ?c ?b)) (min ?a (min ?c ?b))) ==> (< (+ ?a ?a) ?a) if (< ?c 0)
(< (min ?c ?b) ?a) <=> (< (+ ?b (min ?c ?b)) (min ?a (+ ?b ?a))) if  (< ?b 0)
(< (+ ?c (min ?c ?b)) (min ?c (+ ?c ?a))) <=> (< (min ?c ?b) ?a) if  (< ?b 0)
(< (min ?c ?b) ?a) <=> (< (+ ?b (min ?c ?b)) (min ?c (+ ?b ?a))) if  (< ?b 0)
(< ?c (min ?b ?a)) <=> (< (min ?c (+ ?c ?c)) (+ ?c (min ?b ?a))) if  (< ?b 0)
(< (+ ?c ?c) (min ?c (min ?b ?a))) <=> (< (+ ?c ?c) (min ?b ?a)) if  (< ?b 0)
(< (min ?c (+ ?c ?c)) (min ?b ?a)) <=> (< (+ ?c ?c) (min ?b ?a)) if  (< ?b 0)
(< (min ?c (+ ?c ?b)) (+ ?b (min ?b ?a))) <=> (< ?c (min ?b ?a)) if  (< ?b 0)
(< (+ ?b ?c) ?a) <=> (< (+ ?c (+ ?b ?b)) (min ?a (+ ?b ?a))) if  (< ?b 0)
(< ?c (+ ?b ?a)) <=> (< (min ?c (+ ?c ?b)) (+ ?b (+ ?b ?a))) if  (< ?b 0)
(< (+ ?b ?a) (min ?b (min ?a ?c))) ==> (< (+ ?b ?a) (min ?b ?a)) if (< 0 ?c)
(< (+ ?b (min ?a ?c)) (+ ?b (+ ?a ?a))) ==> (< ?b (+ ?b ?a)) if (< 0 ?c)
(< (+ ?a (min ?a ?c)) (min ?a (min ?c ?b))) ==> (< (+ ?a ?a) ?a) if (< 0 ?b)
(< (min ?a (min ?b ?c)) (+ ?a ?a)) ==> (< (min ?a ?b) (+ ?a ?a)) if (< 0 ?c)
(< (+ ?b (min ?a ?c)) (min ?b ?a)) ==> (< (+ ?b ?a) (min ?b ?a)) if (< 0 ?c)
(< (+ ?c (min ?c ?b)) (+ ?b (+ ?b ?a))) <=> (< ?c (+ ?b ?a)) if  (< 0 ?a)
(< (+ ?b ?b) (min ?b (min ?a ?c))) ==> (< (+ ?b ?b) (min ?b ?a)) if (< 0 ?c)
(< (min ?c (+ ?a ?c)) (+ ?c (min ?a ?b))) ==> (< ?a (+ ?a ?a)) if (< 0 ?b)
(< (min ?b (min ?a ?c)) (+ ?b ?a)) ==> (< (min ?b ?a) (+ ?b ?a)) if (< 0 ?c)
(< (min ?b (min ?a ?c)) (+ ?b (min ?b ?a))) ==> (< ?b (+ ?b ?b)) if (< 0 ?c)
(< (+ ?b (min ?a ?c)) ?c) ==> (< (+ ?b (min ?b ?a)) ?a) if (< ?b 0)
(< (+ ?b (min ?a ?c)) ?c) ==> (< (min ?b (+ ?a ?a)) ?a) if (< ?b 0)
(< (+ ?c (min ?a ?b)) ?a) ==> (< (min ?c (+ ?a ?a)) ?a) if (< ?c 0)
(< ?c (min ?a (+ ?c ?b))) <=> (< ?c (min ?c (+ ?b ?a))) if  (< ?b 0)
(< ?c (min ?c (+ ?b ?a))) ==> (< ?c (min ?b (+ ?c ?b))) if (< ?b 0)
(< (+ ?b (min ?a ?c)) ?c) ==> (< (min ?b (+ ?b ?a)) ?a) if (< ?b 0)
(< (+ ?b (min ?a ?c)) ?c) <=> (< (min ?c (+ ?b ?a)) ?a) if  (< ?b 0)
(< ?a (min ?c (+ ?a ?b))) ==> (< ?a (min ?a (+ ?a ?a))) if (< ?b 0)
(< (min ?c (+ ?b ?a)) ?a) ==> (< (min ?b (+ ?c ?c)) ?c) if (< ?b 0)
(< ?c (+ ?b (min ?c ?a))) <=> (< ?c (min ?c (+ ?b ?a))) if  (< ?b 0)
(< (+ ?a (min ?b ?c)) ?a) ==> (< (+ ?a (min ?a ?b)) ?a) if (< ?b 0)
(< (min ?a (+ ?b ?a)) (min ?c (+ ?b ?a))) ==> 0 if (< ?b 0)
(< ?c (+ ?b ?a)) <=> (< ?c (min ?a (+ ?b ?a))) if  (< ?b 0)
(< (min ?c (+ ?c ?b)) ?a) <=> (< (+ ?c ?b) ?a) if  (< ?b 0)
(< (+ ?a (min ?b ?c)) ?a) ==> (< (+ ?a ?b) ?a) if (< 0 ?c)
(< (min ?b (+ ?a ?c)) ?a) ==> (< ?b ?a) if (< 0 ?c)
(< ?c (+ ?c (min ?b ?a))) ==> 0 if (< ?b 0)
(< ?c (min ?c (+ ?b ?a))) ==> 0 if (< ?b 0)
(< (+ ?a (min ?c ?b)) ?a) ==> 1 if (< ?c 0)
(< (min ?c (+ ?a ?b)) ?a) ==> 1 if (< ?b 0)
(< (+ ?c (min ?d ?b)) (min ?a (+ ?b ?a))) <=> (< (+ ?c (min ?d ?b)) (min ?c (+ ?b ?a))) if  (< ?b 0)
(< (+ ?b (+ ?a ?d)) (min ?c (+ ?b ?a))) ==> (< (+ ?d (min ?b ?a)) (min ?a (+ ?b ?d))) if (< 0 ?d)
(< (min ?d (min ?c ?b)) (min ?a (+ ?a ?a))) <=> (< (min ?d (min ?c ?b)) (min ?a (+ ?b ?a))) if  (< 0 ?a)
(< (+ ?c (min ?d ?b)) (+ ?c (+ ?b ?a))) <=> (< (min ?c (min ?d ?b)) (+ ?d (+ ?a ?a))) if  (< 0 ?a)
(< (min ?b (min ?d ?a)) (min ?c (+ ?d ?a))) <=> (< (min ?b (min ?d ?a)) (min ?c (+ ?b ?a))) if  (< 0 ?a)
(< (+ ?d (min ?c ?b)) (min ?c (min ?b ?a))) ==> (< (+ ?d (min ?c ?b)) (min ?b (+ ?c ?d))) if (< 0 ?d)
(< (min ?b (min ?d ?c)) (+ ?d (+ ?a ?a))) <=> (< (min ?b (min ?d ?c)) (+ ?b (+ ?a ?a))) if  (< 0 ?a)
(< (min ?d (+ ?c ?c)) (min ?c (min ?b ?a))) <=> (< (min ?d (+ ?c ?c)) (min ?b ?a)) if  (< ?a 0)
(< (+ ?d ?c) (min ?b (+ ?a ?a))) <=> (< (min ?a (+ ?d ?c)) (min ?b (+ ?a ?a))) if  (< ?b 0)
(< (min ?d (min ?b ?c)) (+ ?b ?a)) <=> (< (min ?d (min ?b ?c)) (min ?a (+ ?b ?a))) if  (< ?b 0)
(< (min ?d (min ?c ?b)) (min ?a (+ ?a ?a))) <=> (< (min ?d (min ?c ?b)) (+ ?a ?a)) if  (< ?c 0)
(< (+ ?c ?d) (+ ?c (+ ?b ?a))) <=> (< (+ ?c (min ?d ?b)) (+ ?c (+ ?b ?a))) if  (< ?a 0)
(< (min ?d ?c) (+ ?b (+ ?a ?a))) <=> (< (min ?d (min ?c ?b)) (+ ?b (+ ?a ?a))) if  (< ?a 0)
(< (+ ?b (min ?d ?c)) (min ?a (+ ?b ?a))) <=> (< (+ ?b (min ?d ?c)) (+ ?b ?a)) if  (< ?b 0)
(< (min ?d (+ ?c ?c)) (min ?b ?a)) <=> (< (min ?d (+ ?c ?c)) (min ?c (min ?b ?a))) if  (< ?d 0)
(< (min ?d (+ ?c ?b)) (min ?c (+ ?a ?a))) <=> (< (min ?d (+ ?c ?b)) (+ ?a ?a)) if  (< ?b 0)
(< (min ?d (+ ?c ?b)) (min ?a (+ ?b ?a))) <=> (< (min ?d (+ ?c ?b)) (+ ?b ?a)) if  (< ?b 0)
(< (min ?d (min ?c ?a)) (min ?b (+ ?a ?a))) <=> (< (min ?d ?c) (min ?b (+ ?a ?a))) if  (< ?b 0)
(< (min ?a (+ ?d ?c)) (+ ?a ?b)) <=> (< (+ ?a (+ ?d ?c)) (+ ?b (+ ?a ?a))) if  (< ?b 0)
(< (min ?d (+ ?c ?b)) (min ?a (+ ?a ?a))) <=> (< (min ?d (+ ?c ?b)) (+ ?a ?a)) if  (< ?d 0)
(< (+ ?d (min ?b ?c)) (+ ?b ?a)) <=> (< (+ ?d (min ?b ?c)) (min ?a (+ ?b ?a))) if  (< ?b 0)
(< (min ?d (min ?c ?b)) (+ ?b (min ?b ?a))) <=> (< (min ?d ?c) (+ ?b (min ?b ?a))) if  (< ?d 0)
(< (+ ?b (+ ?d ?c)) (min ?a (+ ?b ?a))) <=> (< (+ ?b (+ ?d ?c)) (+ ?b ?a)) if  (< ?b 0)
(< (min ?b (min ?d ?a)) (min ?c (+ ?b ?a))) <=> (< (min ?b ?d) (min ?c (+ ?b ?a))) if  (< ?b 0)
(< (+ ?d ?b) (min ?c (+ ?b ?a))) <=> (< (min ?b (+ ?d ?b)) (min ?c (+ ?b ?a))) if  (< ?a 0)
(< (+ ?d (min ?c ?b)) (min ?d (+ ?a ?a))) <=> (< (+ ?d (min ?c ?b)) (+ ?a ?a)) if  (< ?c 0)
(< (min ?d ?b) (+ ?c (min ?b ?a))) <=> (< (min ?d (min ?b ?c)) (+ ?c (min ?b ?a))) if  (< ?b 0)
(< (min ?d (+ ?d ?d)) (min ?c (min ?b ?a))) <=> (< (+ ?d ?d) (min ?c (min ?b ?a))) if  (< ?c 0)
(< (+ ?d (min ?d ?c)) (min ?b ?a)) <=> (< (+ ?d (min ?d ?c)) (min ?d (min ?b ?a))) if  (< ?a 0)
(< (min ?b (+ ?d ?c)) (+ ?b (+ ?a ?a))) <=> (< (+ ?d ?c) (+ ?b (+ ?a ?a))) if  (< ?a 0)
(< (+ ?b ?d) (min ?c (+ ?b ?a))) <=> (< (min ?a (+ ?b ?d)) (min ?c (+ ?b ?a))) if  (< ?b 0)
(< (min ?b (+ ?d ?c)) (min ?a (+ ?b ?a))) <=> (< (+ ?d ?c) (min ?a (+ ?b ?a))) if  (< ?a 0)
(< (+ ?c ?d) (min ?c (+ ?b ?a))) <=> (< (min ?b (+ ?c ?d)) (min ?c (+ ?b ?a))) if  (< ?a 0)
(< (min ?c (+ ?d ?b)) (+ ?c (min ?b ?a))) <=> (< (+ ?d ?b) (+ ?c (min ?b ?a))) if  (< ?b 0)
(< (min ?b (+ ?d ?c)) (+ ?b ?a)) <=> (< (min ?b (+ ?d ?c)) (min ?a (+ ?b ?a))) if  (< ?b 0)
(< (+ ?d (+ ?c ?b)) (+ ?b ?a)) <=> (< (+ ?d (+ ?c ?b)) (+ ?b (min ?d ?a))) if  (< ?c 0)
(< (+ ?a (min ?d ?c)) (+ ?b (+ ?a ?a))) <=> (< (min ?a (min ?d ?c)) (+ ?a ?b)) if  (< ?b 0)
(< (+ ?d ?d) (min ?c (+ ?b ?a))) <=> (< (min ?d (+ ?d ?d)) (min ?c (+ ?b ?a))) if  (< ?c 0)
(< (+ ?b (min ?d ?c)) (min ?b ?a)) <=> (< (+ ?b (min ?d ?c)) (min ?b (min ?d ?a))) if  (< ?b 0)
(< (+ ?d ?b) (+ ?c (min ?b ?a))) <=> (< (min ?a (+ ?d ?b)) (+ ?c (min ?b ?a))) if  (< ?c 0)
(< (min ?d (min ?c ?a)) (min ?b (+ ?a ?a))) <=> (< (min ?d ?c) (min ?b (+ ?a ?a))) if  (< ?c 0)
(< (min ?b (min ?d ?c)) (min ?b (+ ?b ?a))) ==> (< (+ ?b (min ?d ?c)) (+ ?b ?b)) if (< 0 ?a)
(< (+ ?b (+ ?d ?c)) (+ ?c (min ?b ?a))) <=> (< (+ ?b (min ?d ?c)) (min ?b ?a)) if  (< 0 ?c)
(< (min ?d ?c) (min ?b (+ ?b ?a))) <=> (< (min ?d (min ?c ?b)) (min ?b (+ ?c ?a))) if  (< 0 ?a)
(< (min ?d (min ?c ?b)) (+ ?a ?a)) <=> (< (min ?d (min ?c ?b)) (+ ?a (min ?b ?a))) if  (< 0 ?b)
(< (min ?d (+ ?c ?b)) (+ ?a ?a)) <=> (< (min ?d (+ ?c ?b)) (+ ?a (min ?d ?a))) if  (< 0 ?d)
(< (min ?b (min ?d ?c)) (+ ?b ?a)) <=> (< (min ?b (min ?d ?c)) (+ ?d (+ ?a ?a))) if  (< 0 ?a)
(< (+ ?b (min ?d ?c)) (+ ?d (+ ?b ?a))) <=> (< (min ?d (min ?c ?b)) (+ ?b ?a)) if  (< 0 ?a)
(< (min ?d (min ?b ?c)) (+ ?b (min ?b ?a))) ==> (< (min ?d (min ?b ?c)) (+ ?b ?b)) if (< 0 ?a)
(< (min ?d (min ?c ?b)) (+ ?b ?a)) <=> (< (+ ?d (min ?c ?b)) (+ ?c (+ ?d ?a))) if  (< 0 ?a)
(< (+ ?c (min ?d ?b)) (min ?c (+ ?b ?a))) <=> (< (+ ?c ?d) (min ?c (+ ?b ?a))) if  (< 0 ?b)
(< (min ?d (min ?c ?b)) (+ ?a ?a)) <=> (< (min ?d (min ?c ?b)) (+ ?a (min ?b ?a))) if  (< 0 ?a)
(< (min ?c ?d) (+ ?c (min ?b ?a))) <=> (< (+ ?b (min ?c ?d)) (+ ?c (+ ?b ?a))) if  (< 0 ?b)
(< (+ ?c (min ?d ?b)) (min ?c (min ?b ?a))) <=> (< (+ ?c ?d) (min ?c (min ?b ?a))) if  (< 0 ?b)
(< (min ?d (min ?c ?b)) (+ ?b (min ?b ?a))) ==> (< (min ?d (min ?c ?b)) (+ ?b ?b)) if (< 0 ?a)
(< (min ?b ?d) (min ?c (+ ?b ?a))) <=> (< (min ?b (min ?d ?c)) (min ?c (+ ?d ?a))) if  (< 0 ?a)
(< (min ?d (+ ?b ?c)) (min ?b ?a)) <=> (< (+ ?c (min ?d ?b)) (+ ?c (min ?b ?a))) if  (< 0 ?c)
(< (min ?b (+ ?d ?c)) (+ ?b ?a)) <=> (< (+ ?d (min ?c ?b)) (+ ?d (+ ?b ?a))) if  (< 0 ?a)
(< (+ ?d (+ ?c ?b)) (min ?a (+ ?d ?b))) <=> (< (+ ?d (+ ?c ?b)) ?a) if  (< ?c 0)
(< ?d (min ?c (+ ?b ?a))) <=> (< (min ?d (min ?c ?b)) (min ?c (+ ?b ?a))) if  (< ?a 0)
(< (min ?d (min ?b ?a)) (+ ?c (min ?b ?a))) <=> (< ?d (+ ?c (min ?b ?a))) if  (< ?c 0)
(< ?d (+ ?c (+ ?b ?a))) <=> (< (min ?d (+ ?c ?b)) (+ ?c (+ ?b ?a))) if  (< ?a 0)
(< (+ ?a (+ ?b ?d)) (min ?d (+ ?d ?c))) ==> (< (+ ?b (+ ?a ?a)) ?a) if (< 0 ?c)
(< (min ?d (+ ?c ?b)) (min ?c (+ ?b ?a))) <=> (< ?d (min ?c (+ ?b ?a))) if  (< 0 ?b)
(< (min ?b ?d) (min ?c (+ ?b ?a))) <=> (< (+ ?a (min ?b ?d)) (+ ?a ?c)) if  (< 0 ?a)
(< (min ?d (+ ?c ?b)) (min ?c (min ?b ?a))) <=> (< ?d (min ?c (min ?b ?a))) if  (< 0 ?b)
(< (min ?d (min ?c ?b)) (min ?a (+ ?c ?a))) <=> (< (min ?d (min ?c ?b)) ?a) if  (< 0 ?a)
(< (+ ?d ?c) (min ?a (+ ?b ?a))) <=> (< (+ ?d (+ ?c ?b)) (+ ?b ?a)) if  (< 0 ?b)
(< (min ?d ?b) (min ?c (+ ?a ?c))) <=> (< (min ?d ?b) (min ?c (+ ?b ?a))) if  (< 0 ?a)
(< (min ?b (+ ?d ?c)) (min ?b ?a)) <=> (< (+ ?c (min ?b ?d)) (min ?b ?a)) if  (< 0 ?c)
(< (+ ?a (min ?c ?b)) (min ?c (min ?b ?d))) ==> (< ?c (min ?c (+ ?b ?a))) if (< 0 ?a)
(< (min ?d (min ?c ?b)) (min ?a (+ ?b ?b))) <=> (< (min ?d (min ?c ?b)) ?a) if  (< 0 ?b)
(< (min ?d ?c) (min ?b (+ ?b ?a))) <=> (< (min ?d ?c) (+ ?b ?a)) if  (< ?a 0)
(< (+ ?b (min ?d ?c)) (min ?b ?a)) <=> (< (+ ?b (min ?d ?c)) ?a) if  (< ?c 0)
(< ?d (+ ?c (min ?b ?a))) <=> (< (min ?d ?b) (+ ?c (min ?b ?a))) if  (< ?c 0)
(< (+ ?d ?c) (min ?d (+ ?b ?a))) <=> (< (+ ?d ?c) (+ ?b ?a)) if  (< ?c 0)
(< (+ ?d ?c) (+ ?b ?a)) <=> (< (min ?d (+ ?d ?c)) (+ ?b ?a)) if  (< ?c 0)
(< ?d (+ ?c (min ?b ?a))) <=> (< (min ?d ?c) (+ ?c (min ?b ?a))) if  (< ?a 0)
(< (min ?d ?c) (+ ?b ?a)) <=> (< (min ?d (min ?c ?b)) (+ ?b ?a)) if  (< ?a 0)
(< (min ?d (+ ?d ?c)) (min ?b ?a)) <=> (< (+ ?d ?c) (min ?b ?a)) if  (< ?c 0)
(< (+ ?d ?c) (+ ?b ?a)) <=> (< (+ ?d ?c) (min ?b (+ ?b ?a))) if  (< ?a 0)
(< (+ ?d (min ?c ?b)) ?a) <=> (< (+ ?d (min ?c ?b)) (min ?b ?a)) if  (< ?d 0)
(< (min ?d (+ ?c ?b)) (min ?b ?a)) <=> (< (min ?d (+ ?c ?b)) ?a) if  (< ?c 0)
(< (min ?b (min ?d ?c)) (min ?c (+ ?b ?a))) ==> (< (min ?b ?d) ?c) if (< 0 ?a)
(< (min ?d ?c) (min ?b (+ ?b ?a))) ==> (< (min ?d (min ?c ?b)) ?b) if (< 0 ?a)
(< (min ?b ?c) (+ ?b (min ?a ?d))) ==> (< (min ?b ?c) (+ ?b ?a)) if (< 0 ?d)
(< (min ?b ?d) (+ ?c (min ?b ?a))) <=> (< (min ?b ?d) (+ ?c ?a)) if  (< 0 ?c)
(< (min ?d ?c) (min ?b (+ ?b ?a))) ==> (< (min ?d ?c) ?b) if (< 0 ?a)
(< (+ ?d ?c) (min ?b (+ ?b ?a))) ==> (< (+ ?d ?c) ?b) if (< 0 ?a)
(< (min ?b ?d) (min ?c (+ ?b ?a))) ==> (< (min ?b ?d) ?c) if (< 0 ?a)
(< (min ?b (+ ?d ?c)) (+ ?b (+ ?a ?a))) ==> 1 if (< 0 ?a)
(< (+ ?c (+ ?b ?d)) (+ ?c (min ?b ?a))) ==> 0 if (< 0 ?d)
(< (min ?d (+ ?b ?c)) (+ ?c (+ ?b ?a))) ==> 1 if (< 0 ?a)
(< (+ ?b (+ ?a ?d)) (min ?c (+ ?b ?a))) ==> 0 if (< 0 ?d)
(< (min ?b (min ?a ?d)) (+ ?c (min ?b ?a))) ==> 1 if (< 0 ?c)
(< (min ?d (min ?c ?b)) (+ ?b (+ ?a ?a))) ==> 1 if (< 0 ?a)
(< (+ ?b (min ?d ?c)) (+ ?c (+ ?b ?a))) ==> 1 if (< 0 ?a)
(< (min ?b (+ ?d ?c)) (+ ?b ?a)) ==> 1 if (< 0 ?a)
(< (min ?b (min ?d ?c)) (+ ?b ?a)) ==> 1 if (< 0 ?a)
(< ?b ?a) <=> (< (max ?b (+ ?b ?b)) (max ?a (+ ?a ?a)))
(< (+ ?b (max ?c ?b)) (+ ?c (+ ?b ?a))) <=> (< (+ ?a (max ?c ?b)) (+ ?c (+ ?a ?a)))
(< (+ ?c (+ ?b ?b)) (+ ?c (max ?b ?a))) <=> (< (+ ?c (+ ?b ?b)) (max ?c (+ ?c ?a)))
(< (+ ?b (max ?b ?c)) (max ?b (+ ?b ?a))) <=> (< (+ ?a (max ?b ?c)) (max ?a (+ ?a ?a)))
(< (+ ?b (max ?c ?a)) (+ ?b (+ ?a ?a))) <=> (< (max ?b (+ ?b ?c)) (+ ?b (+ ?a ?a)))
(< (+ ?c (+ ?b ?b)) (max ?b (+ ?b ?a))) <=> (< (+ ?b (+ ?c ?a)) (max ?a (+ ?a ?a)))
(< (+ ?b (max ?c ?a)) (+ ?b (+ ?b ?a))) <=> (< (max ?a (+ ?b ?c)) (+ ?b (+ ?b ?a)))
(< (max ?c ?b) (+ ?b (+ ?a ?a))) <=> (< (max ?c (+ ?b ?a)) (+ ?b (+ ?a ?a)))
(< (+ ?c (max ?c ?b)) (+ ?b (max ?b ?a))) <=> (< (+ ?c ?c) (+ ?b (max ?c ?a)))
(< (+ ?b (+ ?a ?c)) (max ?c (+ ?a ?c))) ==> (< (+ ?a (+ ?b ?b)) (max ?b ?a))
(< (+ ?c (max ?c ?a)) (max ?b (+ ?a ?a))) <=> (< (+ ?c ?c) (max ?b (+ ?a ?a)))
(< (+ ?b (+ ?a ?a)) (max ?c (+ ?b ?a))) <=> (< (+ ?b (+ ?a ?a)) (max ?b ?c))
(< (max ?c (+ ?b ?b)) (+ ?a (max ?b ?a))) <=> (< (max ?c (+ ?b ?b)) (+ ?a ?a))
(< (+ ?b (max ?c ?b)) (+ ?a ?a)) <=> (< (+ ?b (max ?c ?b)) (+ ?a (max ?b ?a)))
(< (+ ?c (max ?c ?b)) (+ ?a (max ?b ?a))) <=> (< (+ ?c ?b) (+ ?b ?a))
(< (max ?b ?c) (+ ?b ?a)) <=> (< (max ?b (+ ?c ?a)) (+ ?b (+ ?a ?a)))
(< (+ ?c (max ?b ?a)) (+ ?b (+ ?a ?c))) ==> (< (max ?b ?a) (+ ?b ?a))
(< (+ ?c (max ?a ?b)) (max ?c (+ ?a ?c))) ==> (< (+ ?a (max ?a ?b)) ?a)
(< (+ ?c (+ ?b ?b)) (max ?c (+ ?b ?a))) <=> (< (+ ?c ?b) (max ?c ?a))
(< (+ ?c (max ?b ?a)) (+ ?a (+ ?a ?c))) ==> (< (max ?b ?a) (+ ?a ?a))
(< (+ ?b ?b) (max ?c (+ ?b ?a))) <=> (< (+ ?b ?b) (max ?c (+ ?a ?a)))
(< (+ ?c (max ?c ?b)) (+ ?a ?a)) <=> (< (+ ?c (max ?b ?a)) (+ ?a ?a))
(< (max ?c (+ ?b ?a)) (+ ?a ?a)) <=> (< (max ?c (+ ?b ?b)) (+ ?a ?a))
(< (+ ?c ?c) (+ ?a (max ?b ?a))) <=> (< (+ ?c ?c) (+ ?a (max ?c ?b)))
(< (+ ?b (+ ?c ?d)) (+ ?c (+ ?b ?a))) <=> (< (+ ?d (max ?b ?c)) (+ ?a (max ?b ?c)))
(< (+ ?b (max ?d ?c)) (+ ?b ?a)) <=> (< (+ ?b (max ?d ?c)) (+ ?b (max ?c ?a)))
(< (+ ?b (max ?d ?c)) (+ ?c (max ?b ?a))) <=> (< (+ ?b (max ?d ?c)) (+ ?c ?a))
(< (max ?d (+ ?b ?c)) (+ ?b ?a)) <=> (< (max ?d (+ ?b ?c)) (+ ?b (max ?c ?a)))
(< (max ?d ?c) (+ ?b ?a)) <=> (< (+ ?d (max ?d ?c)) (+ ?d (+ ?b ?a)))
(< (+ ?d (+ ?c ?c)) (+ ?c (max ?b ?a))) <=> (< (+ ?c ?d) (max ?b ?a))
(< (+ ?b (max ?a ?d)) (max ?c (+ ?b ?a))) <=> (< (+ ?b (max ?a ?d)) ?c)
(< (max ?d (+ ?c ?b)) ?a) <=> (< (max ?d (+ ?c ?b)) (max ?d ?a))
(< (max ?b ?a) (+ ?b (+ ?a ?a))) <=> (< (max ?a (+ ?b ?b)) (+ ?b (+ ?a ?a))) if  (< ?a 0)
(< (max ?a (+ ?b ?b)) (+ ?b (+ ?a ?a))) <=> (< ?a (+ ?b (+ ?a ?a))) if  (< ?b 0)
(< (+ ?b (+ ?a ?a)) ?a) <=> (< (+ ?a (+ ?b ?b)) (max ?b (+ ?a ?a))) if  (< ?a 0)
(< ?a (+ ?b (+ ?a ?a))) <=> (< (max ?b (+ ?a ?a)) (+ ?a (+ ?b ?b))) if  (< ?a 0)
(< (+ ?b (+ ?b ?b)) (max ?a (+ ?b ?a))) <=> (< (+ ?b (+ ?b ?b)) ?a) if  (< ?a 0)
(< ?b (+ ?a (+ ?a ?a))) <=> (< (max ?b (+ ?b ?a)) (+ ?a (+ ?a ?a))) if  (< ?b 0)
(< ?b (+ ?a (max ?b ?a))) <=> (< (+ ?b (max ?b ?a)) (+ ?a (+ ?a ?a))) if  (< ?b 0)
(< (+ ?b ?b) ?a) <=> (< (+ ?b (+ ?b ?b)) (+ ?a (max ?b ?a))) if  (< ?a 0)
(< (+ ?b (+ ?b ?b)) (max ?b ?a)) ==> (< (+ ?b ?b) ?b) if (< ?a 0)
(max ?a (+ ?a ?b)) ==> ?a if (< ?b 0)
(< (max ?c (+ ?b ?b)) (max ?a (+ ?b ?a))) <=> (< (max ?c (+ ?b ?b)) (max ?a (+ ?a ?a))) if  (< ?c 0)
(< (+ ?c (max ?c ?b)) (max ?a (+ ?c ?a))) <=> (< (+ ?c (max ?c ?b)) (max ?a (+ ?a ?a))) if  (< ?b 0)
(< (max ?b (max ?c ?a)) (max ?c (+ ?b ?a))) ==> (< (max ?b (+ ?c ?c)) (+ ?b (+ ?b ?b))) if (< ?b 0)
(< (+ ?b (+ ?a ?c)) (+ ?a (max ?a ?c))) ==> (< (+ ?a (+ ?b ?b)) (max ?b (+ ?a ?a))) if (< ?b 0)
(< (+ ?b (max ?a ?c)) (max ?b (max ?a ?c))) ==> (< (+ ?a (+ ?b ?b)) (max ?b (+ ?a ?a))) if (< ?b 0)
(< (+ ?b (max ?a ?c)) (+ ?b (+ ?a ?a))) ==> (< (max ?a (+ ?b ?b)) (+ ?b (+ ?a ?a))) if (< ?a 0)
(< (max ?b (max ?a ?c)) (+ ?a (max ?a ?c))) ==> (< (max ?a (+ ?b ?b)) (+ ?a (+ ?a ?a))) if (< ?b 0)
(< (max ?b (max ?c ?a)) (+ ?b (max ?b ?a))) ==> (< (max ?b (+ ?c ?c)) (+ ?b (+ ?b ?b))) if (< ?b 0)
(< (max ?a (+ ?b ?c)) (max ?c (+ ?b ?a))) <=> (< (+ ?b (+ ?c ?a)) (+ ?b (+ ?c ?c))) if  (< ?b 0)
(< (max ?b (max ?c ?a)) (+ ?b (max ?b ?a))) ==> (< (max ?b (+ ?c ?c)) (+ ?b (+ ?b ?b))) if (< ?c 0)
(< (max ?c (+ ?c ?c)) (max ?a (+ ?b ?a))) <=> (< (max ?c (+ ?c ?c)) (max ?a (+ ?c ?b))) if  (< ?b 0)
(< (+ ?a (+ ?b ?c)) (+ ?a (max ?a ?c))) ==> (< (+ ?a (+ ?b ?b)) (max ?b (+ ?a ?a))) if (< ?b 0)
(< (max ?a (max ?b ?c)) (+ ?b (+ ?b ?c))) ==> (< (max ?a (+ ?a ?a)) (+ ?b (+ ?a ?a))) if (< ?b 0)
(< (max ?c (max ?b ?a)) (max ?b (+ ?b ?a))) ==> (< (max ?b (+ ?c ?c)) (+ ?b (+ ?b ?b))) if (< ?b 0)
(< (max ?c (max ?b ?a)) (max ?a (+ ?b ?a))) ==> (< (max ?b (+ ?c ?c)) (+ ?b (+ ?b ?b))) if (< ?b 0)
(< (max ?c (max ?b ?a)) (max ?c (+ ?b ?a))) ==> (< (max ?b (+ ?c ?c)) (+ ?b (+ ?b ?b))) if (< ?b 0)
(< (max ?b (max ?c ?a)) (max ?b (+ ?b ?a))) ==> (< (max ?b (+ ?c ?c)) (+ ?b (+ ?b ?b))) if (< ?b 0)
(< (max ?c (+ ?c ?b)) (+ ?c (+ ?b ?a))) <=> (< (max ?c (max ?b ?a)) (+ ?b (+ ?a ?a))) if  (< ?c 0)
(< (+ ?b (+ ?c ?a)) (+ ?c (max ?b ?a))) <=> (< (+ ?b (+ ?c ?a)) (+ ?c (max ?c ?a))) if  (< ?b 0)
(< (max ?a (max ?b ?c)) (+ ?a (+ ?b ?b))) ==> (< (max ?a (+ ?a ?a)) (+ ?b (+ ?a ?a))) if (< ?b 0)
(< (+ ?b (max ?c ?b)) (max ?a (+ ?a ?a))) <=> (< (+ ?b (max ?c ?b)) (max ?a (+ ?b ?a))) if  (< ?c 0)
(< (max ?c (+ ?a ?b)) (+ ?a (+ ?b ?b))) ==> (< (max ?a (+ ?a ?a)) (+ ?b (+ ?a ?a))) if (< ?b 0)
(< (max ?a (+ ?b ?c)) (+ ?b (+ ?b ?c))) ==> (< (max ?a (+ ?a ?a)) (+ ?b (+ ?a ?a))) if (< ?b 0)
(< (max ?a (+ ?b ?c)) (max ?c (+ ?a ?c))) ==> (< (+ ?b (max ?a ?b)) (max ?b (+ ?a ?a))) if (< 0 ?c)
(< (max ?c (max ?b ?a)) (+ ?b (+ ?b ?a))) <=> (< (max ?c (+ ?b ?a)) (+ ?b (+ ?b ?a))) if  (< 0 ?a)
(< (+ ?c (max ?c ?b)) (max ?b (+ ?a ?a))) <=> (< (+ ?c (max ?b ?a)) (max ?b (+ ?a ?a))) if  (< 0 ?a)
(< (max ?c (+ ?c ?c)) (+ ?b (max ?c ?a))) <=> (< (max ?c (+ ?c ?c)) (+ ?b (max ?b ?a))) if  (< 0 ?a)
(< (max ?b (+ ?c ?c)) (+ ?b (max ?c ?a))) <=> (< (max ?b (+ ?c ?c)) (+ ?b (max ?b ?a))) if  (< 0 ?a)
(< (+ ?b (+ ?c ?c)) (+ ?a (max ?c ?a))) <=> (< (+ ?b ?c) (max ?a (+ ?b ?a))) if  (< ?b 0)
(< (max ?c (+ ?b ?b)) (+ ?b ?a)) <=> (< (max ?c (+ ?b ?b)) (+ ?b (max ?c ?a))) if  (< ?c 0)
(< (max ?b (+ ?c ?c)) (+ ?b (max ?c ?a))) <=> (< (max ?b (+ ?c ?c)) (+ ?b ?a)) if  (< ?b 0)
(< (+ ?b ?c) (max ?b (+ ?a ?a))) <=> (< (+ ?b (max ?c ?a)) (max ?b (+ ?a ?a))) if  (< ?b 0)
(< (+ ?b (+ ?a ?c)) (+ ?a (max ?a ?c))) ==> (< (+ ?a (+ ?b ?b)) (max ?b ?a)) if (< ?b 0)
(< (max ?c (+ ?c ?c)) (+ ?b ?a)) <=> (< (max ?c (+ ?c ?c)) (+ ?b (max ?c ?a))) if  (< ?b 0)
(< (max ?c (max ?b ?a)) (+ ?b ?a)) ==> (< (max ?b (+ ?c ?c)) (+ ?b (+ ?b ?b))) if (< ?b 0)
(< (max ?c (max ?b ?a)) (+ ?b ?a)) ==> (< (max ?c (+ ?c ?c)) (+ ?b (+ ?c ?c))) if (< ?b 0)
(< (max ?c (+ ?a ?b)) (+ ?b ?c)) ==> (< (max ?a (+ ?a ?a)) (+ ?b (+ ?a ?a))) if (< ?b 0)
(< (max ?b (+ ?c ?a)) (+ ?b ?a)) <=> (< (max ?b (+ ?c ?a)) (+ ?b (max ?c ?a))) if  (< ?c 0)
(< (+ ?c (max ?b ?a)) (+ ?c (+ ?b ?a))) <=> (< (max ?c (max ?b ?a)) (+ ?b ?a)) if  (< ?c 0)
(< (max ?b (max ?a ?c)) (+ ?c (max ?a ?c))) <=> (< (max ?b ?a) (+ ?c (max ?b ?a))) if  (< ?b 0)
(< (max ?b (+ ?c ?b)) (+ ?b (+ ?a ?a))) <=> (< (max ?c (max ?b ?a)) (+ ?a ?a)) if  (< ?b 0)
(< (+ ?c (max ?c ?b)) (max ?c ?a)) <=> (< (+ ?b (+ ?c ?c)) (max ?b (+ ?b ?a))) if  (< ?b 0)
(< (+ ?b (+ ?a ?c)) (+ ?a (max ?b ?a))) <=> (< (+ ?b (max ?a ?c)) (max ?b ?a)) if  (< ?b 0)
(< (max ?b (+ ?c ?b)) (+ ?b ?a)) <=> (< (max ?c (+ ?c ?c)) (+ ?c (max ?b ?a))) if  (< ?b 0)
(< (max ?b (max ?c ?a)) (+ ?b ?a)) ==> (< (max ?b (+ ?c ?c)) (+ ?b (+ ?b ?b))) if (< ?b 0)
(< (max ?a (max ?b ?c)) (+ ?a (max ?a ?c))) ==> (< (max ?a (+ ?b ?b)) (+ ?a ?a)) if (< ?b 0)
(< (+ ?a (+ ?b ?b)) (max ?b (max ?a ?c))) ==> (< (+ ?b (+ ?b ?b)) (max ?b ?a)) if (< ?b 0)
(< (+ ?c ?c) (max ?c (+ ?b ?a))) <=> (< (+ ?c (max ?c ?b)) (max ?c (+ ?b ?a))) if  (< ?b 0)
(< (+ ?b (max ?a ?c)) (+ ?b (+ ?a ?a))) ==> (< (max ?b ?a) (max ?b (+ ?a ?a))) if (< ?a 0)
(< (+ ?c (+ ?b ?a)) (+ ?b (max ?b ?a))) <=> (< (+ ?a (max ?c ?b)) (max ?b ?a)) if  (< ?b 0)
(< (+ ?b (max ?c ?a)) (max ?b (max ?c ?a))) <=> (< (+ ?a (max ?b ?c)) (max ?b ?a)) if  (< ?c 0)
(< (+ ?b (max ?c ?b)) (max ?b (+ ?a ?a))) <=> (< (+ ?c ?b) (max ?c (+ ?c ?a))) if  (< ?c 0)
(< (max ?b (max ?c ?a)) (+ ?b (max ?b ?a))) ==> (< (max ?b ?c) (+ ?b (+ ?b ?b))) if (< ?c 0)
(< (max ?b (max ?a ?c)) (+ ?b (+ ?b ?c))) ==> (< (max ?b ?a) (max ?b (+ ?b ?a))) if (< ?b 0)
(< (+ ?b (max ?a ?c)) (+ ?a (+ ?b ?b))) ==> (< (max ?b ?a) (max ?b (+ ?b ?a))) if (< ?b 0)
(< (+ ?b (max ?a ?c)) (+ ?b (+ ?a ?a))) ==> (< (max ?b ?a) (max ?a (+ ?b ?a))) if (< ?a 0)
(< (+ ?b (max ?a ?c)) (+ ?b (+ ?a ?a))) ==> (< (max ?b ?a) (max ?b (+ ?b ?a))) if (< ?a 0)
(< (+ ?b (+ ?c ?a)) (max ?b ?a)) <=> (< (+ ?b (+ ?c ?a)) (max ?b (max ?c ?a))) if  (< ?c 0)
(< (+ ?c (max ?c ?b)) (max ?c (max ?b ?a))) <=> (< (+ ?c ?c) (max ?c (max ?b ?a))) if  (< ?b 0)
(< (+ ?b (max ?a ?c)) (+ ?b (+ ?a ?c))) ==> (< (max ?b ?a) (+ ?b (+ ?a ?a))) if (< ?a 0)
(< (max ?a (max ?b ?c)) (+ ?b ?b)) ==> (< (max ?a (+ ?a ?a)) (+ ?b (+ ?a ?a))) if (< ?b 0)
(< (max ?b (max ?a ?c)) (+ ?a (+ ?a ?a))) ==> (< (max ?b ?a) (+ ?b (+ ?a ?a))) if (< ?a 0)
(< (max ?b (+ ?b ?b)) (+ ?c (max ?a ?c))) <=> (< (+ ?b ?b) (+ ?c (max ?b ?a))) if  (< 0 ?c)
(< (+ ?b ?c) (+ ?b (max ?b ?a))) <=> (< (max ?b (+ ?c ?a)) (+ ?a (max ?b ?a))) if  (< 0 ?a)
(< (+ ?c (max ?c ?b)) (+ ?b (+ ?b ?a))) <=> (< (+ ?c ?c) (+ ?b (+ ?b ?a))) if  (< 0 ?a)
(< (+ ?c (+ ?c ?c)) (max ?b ?a)) <=> (< (+ ?c (+ ?c ?c)) (max ?c (max ?b ?a))) if  (< 0 ?a)
(< (max ?a (+ ?b ?c)) (max ?c (+ ?a ?c))) ==> (< (+ ?a ?b) (max ?a (+ ?a ?a))) if (< 0 ?c)
(< (max ?a (max ?c ?b)) (+ ?a ?a)) <=> (< (+ ?a (max ?c ?b)) (+ ?a (+ ?a ?a))) if  (< 0 ?b)
(< (+ ?b (+ ?a ?c)) (+ ?b (max ?a ?c))) ==> (< (+ ?b ?a) (max ?b ?a)) if (< ?a 0)
(< (+ ?b ?c) (max ?b ?a)) ==> (< (+ ?b (+ ?c ?c)) (max ?c (+ ?b ?b))) if (< ?c 0)
(< (+ ?b (max ?a ?c)) (+ ?b (+ ?a ?a))) ==> (< ?b (max ?b (+ ?b ?a))) if (< ?a 0)
(< (max ?a (+ ?b ?a)) (+ ?a ?c)) <=> (< (max ?b ?a) (+ ?c (max ?b ?a))) if  (< ?b 0)
(< (max ?c ?b) (+ ?b (max ?c ?a))) <=> (< (max ?c ?b) (max ?c (+ ?b ?a))) if  (< ?c 0)
(< (max ?c ?b) (+ ?c (max ?b ?a))) <=> (< (max ?c ?b) (max ?b (+ ?c ?a))) if  (< ?b 0)
(< (max ?b (max ?c ?a)) (+ ?b (max ?b ?a))) ==> (< ?b (max ?b (+ ?b ?b))) if (< ?c 0)
(< (max ?b (max ?c ?a)) (+ ?b (max ?b ?a))) ==> (< ?b (+ ?b (max ?b ?c))) if (< ?c 0)
(< (max ?c (+ ?c ?b)) (+ ?c (+ ?b ?a))) <=> (< ?c (+ ?c (+ ?b ?a))) if  (< ?b 0)
(< (+ ?c ?b) (max ?b ?a)) ==> (< (+ ?b (+ ?c ?c)) (max ?c (+ ?b ?b))) if (< ?c 0)
(< (max ?b (max ?c ?a)) (+ ?b ?a)) ==> (< (max ?b ?c) (+ ?b (+ ?b ?b))) if (< ?b 0)
(< (max ?c (+ ?c ?a)) (max ?b (+ ?a ?a))) <=> (< ?c (max ?b (+ ?a ?a))) if  (< ?c 0)
(< (+ ?b (max ?c ?b)) (max ?a (+ ?b ?a))) <=> (< (+ ?b (max ?c ?b)) ?a) if  (< ?b 0)
(< (+ ?b (max ?c ?a)) (max ?b ?a)) <=> (< (+ ?a (max ?b ?c)) (max ?b ?a)) if  (< ?c 0)
(< (max ?c ?b) (max ?a (+ ?c ?b))) <=> (< (max ?c ?b) (max ?c (max ?b ?a))) if  (< ?b 0)
(< (max ?b ?c) (max ?b (+ ?a ?a))) <=> (< (max ?b ?c) (+ ?a (max ?c ?a))) if  (< ?c 0)
(< (+ ?b (+ ?c ?c)) (+ ?b ?a)) <=> (< (+ ?c ?c) (max ?a (+ ?b ?a))) if  (< ?b 0)
(< (max ?b ?c) (+ ?a (max ?b ?a))) <=> (< (max ?b ?c) (max ?b (+ ?a ?a))) if  (< ?b 0)
(< ?b (+ ?b (max ?c ?a))) <=> (< (max ?b (+ ?b ?c)) (+ ?b (+ ?a ?a))) if  (< ?c 0)
(< (max ?c ?b) (max ?a (+ ?b ?a))) <=> (< (max ?c ?b) (max ?c (max ?b ?a))) if  (< ?b 0)
(< (max ?c ?b) (max ?c (+ ?c ?a))) <=> (< (max ?c ?b) (+ ?c (max ?b ?a))) if  (< ?b 0)
(< (max ?c ?b) (max ?b (+ ?c ?a))) <=> (< (max ?c ?b) (+ ?c (max ?b ?a))) if  (< ?c 0)
(< (max ?c ?b) (max ?c (+ ?c ?a))) <=> (< (max ?c ?b) (+ ?c (max ?b ?a))) if  (< ?c 0)
(< (max ?c ?b) (+ ?b (max ?c ?a))) <=> (< (max ?c ?b) (max ?b (+ ?b ?a))) if  (< ?c 0)
(< (+ ?b (+ ?a ?c)) (+ ?b (+ ?a ?a))) <=> (< (max ?c (+ ?b ?a)) ?a) if  (< ?b 0)
(< (max ?b (+ ?a ?a)) (max ?c (+ ?b ?a))) <=> (< (max ?b (+ ?a ?a)) ?c) if  (< ?b 0)
(< (max ?b (+ ?b ?a)) (+ ?c (max ?b ?a))) <=> (< ?b (+ ?c (max ?b ?a))) if  (< ?a 0)
(< (max ?c (+ ?b ?c)) (max ?b ?a)) <=> (< (+ ?b ?c) (+ ?b (max ?b ?a))) if  (< ?c 0)
(< (+ ?c (max ?c ?b)) (max ?a (+ ?b ?a))) <=> (< (+ ?c (max ?c ?b)) ?a) if  (< ?b 0)
(< (+ ?b ?b) (max ?b (max ?c ?a))) <=> (< (+ ?b (max ?b ?c)) (max ?b ?a)) if  (< ?c 0)
(< ?c (+ ?b (max ?b ?a))) <=> (< (max ?c (+ ?c ?b)) (+ ?b (max ?b ?a))) if  (< ?c 0)
(< (max ?c ?b) (max ?a (+ ?c ?c))) <=> (< (max ?c ?b) (max ?c (max ?b ?a))) if  (< ?c 0)
(< (max ?b (max ?a ?c)) (+ ?b ?a)) ==> (< (max ?b ?a) (+ ?a (+ ?a ?a))) if (< ?a 0)
(< (max ?c (max ?a ?b)) (+ ?a ?a)) ==> (< (max ?a (+ ?c ?c)) (+ ?c ?a)) if (< ?a 0)
(< ?c (max ?b (+ ?a ?a))) <=> (< (max ?c (+ ?b ?a)) (max ?b (+ ?a ?a))) if  (< ?b 0)
(< (+ ?a (+ ?b ?c)) (max ?c (+ ?a ?b))) ==> (< (+ ?b (+ ?a ?a)) ?a) if (< 0 ?c)
(< (max ?b (max ?a ?c)) (+ ?c (max ?b ?a))) ==> (< ?b (+ ?b (max ?b ?a))) if (< 0 ?c)
(< (max ?a (+ ?c ?b)) (+ ?c (+ ?b ?a))) ==> (< ?c (+ ?b (+ ?c ?c))) if (< 0 ?a)
(< (+ ?c ?c) (max ?b ?a)) <=> (< (+ ?c (max ?c ?b)) (max ?b ?a)) if  (< ?b 0)
(< (max ?b ?a) (+ ?c (max ?b ?a))) <=> (< ?b (+ ?b (max ?a ?c))) if  (< ?a 0)
(< (max ?b (max ?c ?a)) (+ ?b (max ?b ?a))) ==> (< ?b (+ ?b ?b)) if (< ?c 0)
(< (max ?c ?b) (+ ?a ?a)) <=> (< (max ?c ?b) (+ ?a (max ?b ?a))) if  (< ?b 0)
(< (+ ?c (+ ?a ?b)) (+ ?a ?a)) <=> (< (+ ?c (max ?a ?b)) ?a) if  (< ?c 0)
(< (max ?c ?b) (+ ?b ?a)) <=> (< (max ?c ?b) (+ ?b (max ?c ?a))) if  (< ?c 0)
(< (+ ?a (max ?c ?b)) ?a) <=> (< (+ ?a (+ ?c ?b)) (+ ?a ?c)) if  (< ?c 0)
(< ?c (max ?c (max ?b ?a))) <=> (< (max ?c (+ ?b ?b)) (max ?b ?a)) if  (< ?b 0)
(< (+ ?b (+ ?a ?a)) (max ?b ?c)) ==> (< (+ ?b ?a) (max ?b ?a)) if (< ?a 0)
(< (max ?c ?b) (+ ?c (max ?b ?a))) <=> (< (max ?c ?b) (+ ?c ?a)) if  (< ?b 0)
(< (+ ?b ?c) ?a) <=> (< (+ ?c (+ ?b ?b)) (+ ?a (max ?b ?a))) if  (< ?c 0)
(< (max ?b (max ?a ?c)) (+ ?a (max ?b ?c))) ==> (< ?b (+ ?b ?a)) if (< 0 ?c)
(< (+ ?a (+ ?c ?b)) (+ ?c (max ?a ?b))) ==> (< (+ ?a ?a) ?a) if (< 0 ?b)
(< (max ?a (max ?c ?b)) (+ ?a (max ?c ?b))) ==> (< ?a (+ ?a ?a)) if (< 0 ?b)
(< (+ ?a (max ?c ?b)) (max ?c (+ ?a ?a))) <=> (< (max ?c ?b) ?a) if  (< 0 ?a)
(< (+ ?b (max ?a ?c)) (+ ?b (+ ?a ?c))) ==> (< ?b (+ ?b ?a)) if (< 0 ?c)
(< (max ?a (+ ?b ?c)) (+ ?a ?c)) ==> (< (+ ?a ?b) (+ ?a ?a)) if (< 0 ?c)
(< (max ?c (+ ?c ?b)) ?a) <=> (< ?c (max ?a (+ ?c ?b))) if  (< ?b 0)
(< ?c (+ ?b ?a)) <=> (< (max ?c (+ ?c ?c)) (+ ?b ?a)) if  (< ?c 0)
(< (max ?c ?b) ?a) <=> (< (max ?c ?b) (max ?a (+ ?c ?b))) if  (< ?c 0)
(< (max ?c (+ ?c ?b)) (max ?b ?a)) <=> (< ?c (max ?b ?a)) if  (< ?c 0)
(< (max ?c (+ ?b ?a)) (max ?b ?a)) <=> (< ?c (max ?b ?a)) if  (< ?b 0)
(< (max ?c (+ ?c ?b)) (max ?b ?a)) <=> (< ?c (max ?b ?a)) if  (< ?b 0)
(< (+ ?c ?b) ?a) <=> (< (+ ?c ?b) (max ?a (+ ?b ?a))) if  (< ?b 0)
(< (max ?c ?b) ?a) <=> (< (max ?c ?b) (max ?a (+ ?c ?a))) if  (< ?c 0)
(< (max ?c (+ ?b ?a)) ?a) <=> (< ?c (max ?a (+ ?c ?b))) if  (< ?b 0)
(< (+ ?c ?b) (+ ?b ?a)) <=> (< ?c (max ?a (+ ?c ?b))) if  (< ?b 0)
(< (+ ?b ?a) (max ?b ?c)) ==> (< (+ ?b ?a) (max ?b ?a)) if (< ?a 0)
(< (+ ?b (max ?c ?a)) ?a) <=> (< (max ?c (+ ?a ?b)) ?a) if  (< 0 ?b)
(< ?c (+ ?b ?a)) <=> (< ?c (+ ?b (max ?c ?a))) if  (< ?b 0)
(< (+ ?c ?b) ?a) <=> (< (+ ?c (max ?b ?a)) ?a) if  (< ?c 0)
(< ?c (+ ?c (max ?b ?a))) ==> 1 if (< 0 ?a)
(< (max ?c (+ ?a ?b)) ?a) ==> 0 if (< 0 ?b)
(< ?b (+ ?c (max ?b ?a))) ==> 1 if (< 0 ?c)
(< ?b (max ?c (+ ?b ?a))) ==> 1 if (< 0 ?a)
(< (+ ?a (max ?c ?b)) ?a) ==> 0 if (< 0 ?b)
(< (max ?b (+ ?d ?b)) (max ?c (+ ?b ?a))) ==> (< (max ?b (+ ?d ?b)) (max ?c (+ ?d ?b))) if (< ?a 0)
(< (max ?b (max ?c ?d)) (+ ?c (max ?b ?a))) ==> (< (max ?b (max ?c ?d)) (max ?c (+ ?b ?c))) if (< ?a 0)
(< (max ?c (+ ?d ?c)) (max ?b (+ ?b ?a))) ==> (< (max ?c (+ ?d ?c)) (max ?b (+ ?d ?c))) if (< ?a 0)
(< (max ?b (max ?c ?d)) (max ?b (+ ?c ?a))) <=> (< (max ?b (max ?c ?d)) (+ ?c (max ?b ?a))) if  (< ?c 0)
(< (max ?b (max ?a ?d)) (max ?c (+ ?b ?a))) <=> (< (max ?b (max ?a ?d)) (max ?c (+ ?a ?a))) if  (< ?a 0)
(< (max ?d (max ?b ?c)) (+ ?b (max ?b ?a))) ==> (< (max ?d (max ?b ?c)) (max ?b (+ ?b ?b))) if (< ?a 0)
(< (max ?d (+ ?b ?a)) (max ?c (+ ?a ?d))) <=> (< (max ?d (+ ?b ?a)) (max ?c (+ ?b ?a))) if  (< ?a 0)
(< (+ ?b (+ ?d ?c)) (+ ?c (max ?b ?a))) ==> (< (+ ?b (+ ?d ?d)) (max ?d (+ ?b ?b))) if (< ?d 0)
(< (max ?c (max ?b ?d)) (+ ?c (max ?b ?a))) ==> (< (max ?c (max ?b ?d)) (max ?c (+ ?c ?b))) if (< ?a 0)
(< (max ?c (max ?b ?d)) (+ ?c (max ?b ?a))) ==> (< (max ?c (max ?b ?d)) (max ?b (+ ?c ?b))) if (< ?a 0)
(< (max ?a (max ?d ?c)) (max ?b (+ ?a ?a))) <=> (< (max ?a (max ?d ?c)) (max ?b (+ ?a ?d))) if  (< ?a 0)
(< (max ?b (max ?c ?d)) (+ ?c (max ?b ?a))) <=> (< (max ?b (max ?c ?d)) (max ?d (+ ?c ?a))) if  (< ?c 0)
(< (max ?d (+ ?b ?c)) (max ?b (+ ?b ?a))) ==> (< (max ?d (+ ?b ?c)) (max ?b (+ ?b ?c))) if (< ?a 0)
(< (+ ?b (max ?c ?d)) (+ ?c (+ ?b ?a))) <=> (< (max ?c (+ ?d ?b)) (+ ?d (+ ?b ?a))) if  (< ?a 0)
(< (max ?d (max ?b ?c)) (+ ?a (max ?b ?a))) <=> (< (max ?d (max ?b ?c)) (max ?d (+ ?a ?a))) if  (< ?b 0)
(< (max ?d (max ?b ?c)) (+ ?b (max ?b ?a))) ==> (< (max ?d (max ?b ?c)) (max ?d (+ ?b ?b))) if (< ?a 0)
(< (max ?b (max ?a ?d)) (+ ?c (max ?b ?a))) <=> (< (max ?b (max ?a ?d)) (+ ?a (+ ?c ?c))) if  (< ?c 0)
(< (max ?a (+ ?b ?d)) (max ?c (+ ?b ?c))) <=> (< (max ?a (+ ?b ?d)) (max ?c (+ ?b ?a))) if  (< ?b 0)
(< (max ?b (max ?c ?d)) (max ?c (+ ?c ?a))) <=> (< (max ?b (max ?c ?d)) (+ ?c (max ?b ?a))) if  (< ?b 0)
(< (max ?b (max ?c ?d)) (+ ?c (max ?b ?a))) <=> (< (max ?b (max ?c ?d)) (max ?c (+ ?c ?a))) if  (< ?c 0)
(< (max ?d (max ?b ?c)) (+ ?b (max ?b ?a))) ==> (< (max ?d (max ?b ?c)) (max ?c (+ ?b ?b))) if (< ?a 0)
(< (max ?d (+ ?b ?a)) (max ?c (+ ?d ?b))) <=> (< (max ?d (+ ?b ?a)) (max ?c (+ ?b ?a))) if  (< ?b 0)
(< (max ?b (max ?d ?c)) (+ ?b (max ?c ?a))) <=> (< (max ?b (max ?d ?c)) (max ?b (+ ?b ?a))) if  (< ?b 0)
(< (max ?d (max ?c ?b)) (max ?b (+ ?b ?a))) <=> (< (max ?d (max ?c ?b)) (+ ?b (max ?c ?a))) if  (< ?c 0)
(< (max ?b (max ?c ?d)) (max ?d (+ ?c ?a))) <=> (< (max ?b (max ?c ?d)) (+ ?c (max ?b ?a))) if  (< ?b 0)
(< (max ?d (max ?b ?c)) (max ?d (+ ?c ?a))) <=> (< (max ?d (max ?b ?c)) (max ?b (+ ?b ?a))) if  (< ?a 0)
(< (max ?b (max ?d ?c)) (+ ?d (+ ?a ?a))) <=> (< (max ?b (max ?d ?c)) (max ?b (+ ?b ?a))) if  (< ?a 0)
(< (max ?d (max ?b ?c)) (max ?b (+ ?a ?a))) <=> (< (max ?d (max ?b ?c)) (+ ?a (max ?d ?a))) if  (< ?a 0)
(< (max ?b (max ?d ?c)) (max ?c (+ ?b ?a))) <=> (< (max ?b (max ?d ?c)) (+ ?b (max ?c ?a))) if  (< ?b 0)
(< (max ?d (max ?b ?c)) (+ ?a (max ?b ?a))) <=> (< (max ?d (max ?b ?c)) (max ?c (+ ?a ?a))) if  (< ?a 0)
(< (max ?d (max ?b ?c)) (+ ?a (max ?b ?a))) <=> (< (max ?d (max ?b ?c)) (max ?d (+ ?a ?a))) if  (< ?a 0)
(< (max ?c (max ?d ?b)) (+ ?b (max ?c ?a))) <=> (< (max ?c (max ?d ?b)) (max ?c (+ ?b ?a))) if  (< ?c 0)
(< (max ?d (+ ?b ?a)) (max ?c (+ ?d ?c))) <=> (< (max ?d (+ ?b ?a)) (max ?c (+ ?b ?a))) if  (< ?c 0)
(< (max ?b (max ?c ?d)) (+ ?c (max ?b ?a))) <=> (< (max ?b (max ?c ?d)) (max ?b (+ ?c ?a))) if  (< ?b 0)
(< (max ?d (max ?b ?c)) (+ ?a (max ?b ?a))) <=> (< (max ?d (max ?b ?c)) (max ?b (+ ?a ?a))) if  (< ?b 0)
(< (max ?c (max ?d ?b)) (+ ?d (+ ?a ?a))) <=> (< (+ ?b (max ?c ?d)) (+ ?c (+ ?b ?a))) if  (< ?a 0)
(< (+ ?a (+ ?b ?c)) (max ?d (+ ?a ?c))) ==> (< (+ ?a (+ ?b ?b)) (max ?b (+ ?a ?a))) if (< ?b 0)
(< (max ?b (max ?d ?a)) (+ ?c (max ?b ?a))) <=> (< (max ?b (max ?d ?a)) (+ ?c (max ?d ?a))) if  (< ?c 0)
(< (max ?a (+ ?b ?d)) (+ ?a (+ ?c ?c))) <=> (< (max ?b (max ?d ?a)) (+ ?c (max ?b ?a))) if  (< ?c 0)
(< (max ?b (max ?c ?d)) (+ ?c (max ?c ?a))) <=> (< (max ?b (max ?c ?d)) (+ ?c (max ?b ?a))) if  (< ?c 0)
(< (max ?d (+ ?b ?a)) (max ?c (+ ?b ?a))) <=> (< (max ?d (+ ?b ?a)) (max ?c (+ ?a ?c))) if  (< ?a 0)
(< (max ?c (max ?b ?d)) (+ ?c (max ?b ?a))) ==> (< (max ?c (max ?b ?d)) (max ?d (+ ?c ?b))) if (< ?a 0)
(< (max ?d (max ?b ?c)) (+ ?a (max ?b ?a))) <=> (< (max ?d (max ?b ?c)) (max ?c (+ ?a ?a))) if  (< ?b 0)
(< (max ?d (max ?c ?b)) (max ?c (max ?b ?a))) <=> (< (max ?d (max ?c ?b)) (max ?a (+ ?c ?a))) if  (< ?a 0)
(< (max ?c (max ?b ?d)) (max ?c (max ?b ?a))) <=> (< (max ?c (max ?b ?d)) (max ?a (+ ?b ?a))) if  (< ?b 0)
(< (max ?c (max ?b ?d)) (max ?c (max ?b ?a))) <=> (< (max ?c (max ?b ?d)) (max ?a (+ ?b ?b))) if  (< ?b 0)
(< (max ?b (max ?d ?c)) (+ ?a (max ?b ?a))) <=> (< (max ?b (max ?d ?c)) (max ?b (+ ?a ?a))) if  (< ?a 0)
(< (+ ?c ?d) (max ?c (max ?b ?a))) <=> (< (+ ?c (max ?d ?b)) (max ?c (max ?b ?a))) if  (< ?c 0)
(< (+ ?d (max ?b ?c)) (max ?b ?a)) <=> (< (+ ?d (+ ?b ?c)) (+ ?b (max ?b ?a))) if  (< ?d 0)
(< (max ?b (max ?c ?d)) (+ ?c ?a)) <=> (< (max ?b (max ?c ?d)) (+ ?c (max ?b ?a))) if  (< ?b 0)
(< (max ?b (+ ?d ?c)) (+ ?b (max ?b ?a))) <=> (< (max ?b (+ ?d ?c)) (+ ?b ?a)) if  (< ?b 0)
(< (max ?d (max ?b ?c)) (+ ?b (max ?b ?a))) ==> (< (max ?d (max ?b ?c)) (+ ?b ?b)) if (< ?a 0)
(< (max ?b (max ?d ?c)) (max ?d (+ ?c ?a))) <=> (< (max ?b (max ?d ?c)) (+ ?b ?a)) if  (< ?a 0)
(< (max ?c (+ ?d ?b)) (+ ?c (max ?b ?a))) <=> (< (max ?c (+ ?d ?b)) (+ ?c ?a)) if  (< ?b 0)
(< (+ ?d (max ?d ?c)) (max ?c (max ?b ?a))) <=> (< (+ ?d ?d) (max ?c (max ?b ?a))) if  (< ?c 0)
(< (+ ?c (+ ?d ?b)) (+ ?c (max ?b ?a))) <=> (< (+ ?b (max ?c ?d)) (max ?b ?a)) if  (< ?c 0)
(< (+ ?b ?c) (max ?c (+ ?a ?d))) ==> (< (+ ?b (+ ?c ?a)) (+ ?c (max ?b ?a))) if (< ?b 0)
(< (+ ?c ?d) (max ?c (max ?b ?a))) ==> (< (+ ?c (+ ?d ?d)) (max ?d (+ ?c ?c))) if (< ?d 0)
(< (max ?b (max ?d ?c)) (max ?b (+ ?b ?a))) <=> (< (max ?b (max ?d ?c)) (+ ?c ?a)) if  (< ?a 0)
(< (max ?d (max ?c ?b)) (+ ?a ?a)) <=> (< (max ?d (max ?c ?b)) (+ ?a (max ?b ?a))) if  (< ?a 0)
(< (max ?b (+ ?d ?c)) (+ ?b ?a)) <=> (< (max ?d (+ ?c ?b)) (+ ?d (+ ?a ?a))) if  (< ?a 0)
(< (max ?d (max ?c ?b)) (max ?a (+ ?c ?c))) <=> (< (max ?d (max ?c ?b)) (max ?b ?a)) if  (< ?c 0)
(< (max ?d (+ ?c ?b)) (+ ?b ?a)) <=> (< (max ?d (+ ?c ?b)) (+ ?b (max ?d ?a))) if  (< ?b 0)
(< (max ?b (max ?d ?c)) (max ?b ?a)) <=> (< (max ?b (max ?d ?c)) (max ?a (+ ?b ?a))) if  (< ?b 0)
(< (max ?d (max ?c ?b)) (max ?a (+ ?c ?a))) <=> (< (max ?d (max ?c ?b)) (max ?b ?a)) if  (< ?a 0)
(< (max ?d (max ?c ?b)) (+ ?a ?a)) <=> (< (max ?d (max ?c ?b)) (+ ?a (max ?d ?a))) if  (< ?d 0)
(< (+ ?d (max ?d ?c)) (max ?c (+ ?b ?a))) <=> (< (+ ?d ?d) (max ?c (+ ?b ?a))) if  (< ?c 0)
(< (max ?b (max ?d ?c)) (+ ?b ?a)) <=> (< (max ?b (max ?d ?c)) (+ ?b (max ?d ?a))) if  (< ?b 0)
(< (max ?d (max ?c ?b)) (+ ?b (max ?c ?a))) <=> (< (max ?d (max ?c ?b)) (+ ?b ?a)) if  (< ?c 0)
(< (max ?d (+ ?c ?c)) (max ?b ?a)) <=> (< (max ?d (+ ?c ?c)) (max ?c (max ?b ?a))) if  (< 0 ?a)
(< (+ ?d (max ?d ?c)) (max ?d (max ?b ?a))) <=> (< (+ ?d (max ?d ?c)) (max ?b ?a)) if  (< 0 ?a)
(< (max ?d ?c) (+ ?b (+ ?a ?a))) <=> (< (max ?d (max ?c ?b)) (+ ?b (+ ?a ?a))) if  (< 0 ?a)
(< (max ?d (+ ?c ?c)) (max ?c (max ?b ?a))) <=> (< (max ?d (+ ?c ?c)) (max ?b ?a)) if  (< 0 ?b)
(< (max ?b (+ ?d ?c)) (+ ?b (+ ?a ?a))) <=> (< (+ ?d ?c) (+ ?b (+ ?a ?a))) if  (< 0 ?a)
(< (+ ?d ?c) (max ?b (+ ?a ?a))) <=> (< (max ?a (+ ?d ?c)) (max ?b (+ ?a ?a))) if  (< 0 ?b)
(< (+ ?c (max ?d ?c)) (max ?c (max ?b ?a))) <=> (< (+ ?c (max ?d ?c)) (max ?b ?a)) if  (< 0 ?a)
(< (+ ?c (max ?d ?b)) (+ ?c (+ ?b ?a))) <=> (< (+ ?c ?d) (+ ?c (+ ?b ?a))) if  (< 0 ?a)
(< (+ ?c (max ?d ?c)) (max ?b ?a)) <=> (< (+ ?c (max ?d ?c)) (max ?c (max ?b ?a))) if  (< 0 ?b)
(< (+ ?a (+ ?d ?c)) (+ ?b (+ ?a ?a))) <=> (< (max ?a (+ ?d ?c)) (+ ?a ?b)) if  (< 0 ?b)
(< (max ?d (+ ?d ?d)) (max ?c (max ?b ?a))) <=> (< (+ ?d ?d) (max ?c (max ?b ?a))) if  (< 0 ?a)
(< (+ ?b (+ ?d ?c)) (+ ?b ?a)) <=> (< (+ ?b (+ ?d ?c)) (+ ?b (max ?d ?a))) if  (< 0 ?c)
(< (max ?d (+ ?d ?d)) (max ?c (max ?b ?a))) <=> (< (+ ?d ?d) (max ?c (max ?b ?a))) if  (< 0 ?b)
(< (max ?d (+ ?c ?b)) (+ ?a ?a)) <=> (< (max ?d (+ ?c ?b)) (max ?a (+ ?a ?a))) if  (< 0 ?d)
(< (+ ?d (+ ?c ?b)) (max ?a (+ ?c ?a))) <=> (< (+ ?d (+ ?c ?b)) ?a) if  (< ?c 0)
(< (+ ?b (+ ?a ?c)) (max ?d (+ ?b ?c))) ==> (< (+ ?b ?a) (max ?b ?a)) if (< ?a 0)
(< (max ?d (+ ?d ?c)) (+ ?c (+ ?b ?a))) <=> (< ?d (+ ?c (+ ?b ?a))) if  (< ?c 0)
(< (max ?d (+ ?d ?b)) (+ ?c (max ?b ?a))) <=> (< ?d (+ ?c (max ?b ?a))) if  (< ?b 0)
(< (max ?d (+ ?d ?b)) (max ?c (+ ?b ?a))) <=> (< ?d (max ?c (+ ?b ?a))) if  (< ?b 0)
(< (max ?d (+ ?c ?b)) (max ?a (+ ?d ?a))) <=> (< (max ?d (+ ?c ?b)) ?a) if  (< ?d 0)
(< (max ?c ?b) (+ ?b (max ?a ?d))) ==> (< (max ?c ?b) (max ?c (+ ?b ?a))) if (< ?d 0)
(< (+ ?b ?c) (max ?b (+ ?a ?d))) ==> (< (+ ?b (+ ?c ?c)) (max ?b ?a)) if (< ?c 0)
(< (max ?d ?c) (+ ?a (max ?d ?b))) <=> (< (max ?d ?c) (max ?c (+ ?b ?a))) if  (< ?a 0)
(< ?d (max ?c (+ ?b ?a))) <=> (< (max ?d (+ ?d ?c)) (max ?c (+ ?b ?a))) if  (< ?c 0)
(< (+ ?d ?c) (max ?c (+ ?b ?a))) ==> (< (+ ?d ?c) (max ?d (max ?c ?b))) if (< ?d 0)
(< (max ?d (max ?c ?b)) ?a) <=> (< (max ?d (max ?c ?b)) (max ?a (+ ?c ?b))) if  (< ?c 0)
(< (max ?b ?c) (+ ?b (max ?a ?d))) ==> (< (max ?b ?c) (max ?c (+ ?b ?a))) if (< ?d 0)
(< (max ?c ?b) (+ ?b (max ?a ?d))) ==> (< (max ?c ?b) (max ?b (+ ?b ?a))) if (< ?d 0)
(< (+ ?d ?c) (max ?c (+ ?b ?a))) ==> (< (+ ?c (+ ?d ?d)) (max ?d ?c)) if (< ?d 0)
(< (max ?d (+ ?d ?c)) (+ ?c (max ?b ?a))) <=> (< ?d (+ ?c (max ?b ?a))) if  (< ?c 0)
(< (max ?d (+ ?c ?b)) (max ?b ?a)) <=> (< (max ?d (+ ?d ?c)) (max ?b ?a)) if  (< ?c 0)
(< (max ?b ?d) (+ ?c (max ?b ?a))) <=> (< (max ?b ?d) (+ ?c (max ?d ?a))) if  (< ?c 0)
(< (+ ?b (+ ?d ?c)) ?a) <=> (< (+ ?b (+ ?d ?c)) (max ?a (+ ?b ?a))) if  (< ?b 0)
(< (max ?d (+ ?d ?c)) (+ ?b ?a)) <=> (< (+ ?d ?c) (+ ?c (+ ?b ?a))) if  (< ?c 0)
(< (max ?d (+ ?c ?b)) ?a) <=> (< (max ?d (+ ?c ?b)) (max ?a (+ ?c ?a))) if  (< ?c 0)
(< (+ ?d ?c) (+ ?c (max ?b ?a))) <=> (< (max ?d (+ ?d ?c)) (max ?b ?a)) if  (< ?c 0)
(< (max ?d (max ?c ?b)) (max ?a (+ ?c ?a))) <=> (< (max ?d (max ?c ?b)) ?a) if  (< ?c 0)
(< (+ ?d (max ?c ?b)) ?a) <=> (< (+ ?d (max ?c ?b)) (max ?a (+ ?c ?a))) if  (< ?c 0)
(< (+ ?c ?b) (max ?b (max ?a ?d))) ==> (< (+ ?b (+ ?c ?c)) (max ?b ?a)) if (< ?c 0)
(< (max ?d (+ ?d ?c)) (max ?c (max ?b ?a))) <=> (< ?d (max ?c (max ?b ?a))) if  (< ?c 0)
(< (+ ?a (+ ?b ?d)) (max ?d (+ ?d ?c))) ==> (< (+ ?b (+ ?a ?a)) ?a) if (< ?c 0)
(< (+ ?b (+ ?a ?d)) (+ ?d (max ?a ?c))) ==> (< (+ ?b ?a) (max ?b ?a)) if (< ?b 0)
(< ?d (max ?c (max ?b ?a))) <=> (< (max ?d (+ ?c ?b)) (max ?c (max ?b ?a))) if  (< ?c 0)
(< (+ ?b (+ ?a ?d)) (+ ?b (max ?d ?c))) ==> (< (+ ?b ?a) (max ?b ?a)) if (< ?a 0)
(< (max ?c (+ ?d ?c)) (max ?b ?a)) <=> (< (+ ?d ?c) (+ ?d (max ?b ?a))) if  (< ?d 0)
(< (+ ?c ?d) (max ?c (+ ?b ?a))) ==> (< (+ ?c ?d) (max ?d (+ ?c ?c))) if (< ?d 0)
(< (max ?d ?c) (max ?d (+ ?b ?a))) <=> (< (max ?d ?c) (max ?b (+ ?b ?a))) if  (< 0 ?a)
(< (max ?d (+ ?c ?b)) (+ ?c (+ ?b ?a))) <=> (< ?d (+ ?c (+ ?b ?a))) if  (< 0 ?a)
(< (max ?d (max ?c ?b)) (max ?c (+ ?b ?a))) <=> (< (max ?d ?c) (+ ?b ?a)) if  (< 0 ?a)
(< (max ?d ?c) (max ?c (+ ?b ?a))) <=> (< (max ?d ?c) (max ?b (+ ?b ?a))) if  (< 0 ?a)
(< (+ ?b ?a) (max ?b (max ?d ?c))) ==> (< (+ ?b ?a) (max ?b ?a)) if (< ?a 0)
(< (+ ?d ?c) (max ?c (+ ?b ?a))) ==> (< (+ ?d ?d) (max ?d ?c)) if (< ?d 0)
(< (+ ?d (max ?c ?b)) (max ?b ?a)) <=> (< (+ ?d ?c) (max ?b ?a)) if  (< ?d 0)
(< (max ?b ?c) (+ ?b (max ?a ?d))) ==> (< (max ?b ?c) (+ ?b ?a)) if (< ?d 0)
(< (+ ?b ?a) (max ?b (+ ?d ?c))) ==> (< (+ ?b ?a) (max ?b ?a)) if (< ?a 0)
(< (max ?d ?c) (+ ?b ?a)) <=> (< (max ?d ?c) (+ ?a (max ?c ?b))) if  (< ?a 0)
(< (+ ?c ?b) (max ?b (+ ?a ?d))) ==> (< (+ ?c ?b) (max ?b ?a)) if (< ?c 0)
(< ?d (max ?c (+ ?b ?a))) <=> (< (max ?d ?b) (max ?c (+ ?b ?a))) if  (< 0 ?a)
(< (max ?d (max ?c ?b)) (+ ?b ?a)) <=> (< (max ?d ?c) (+ ?b ?a)) if  (< 0 ?a)
(< (max ?d (+ ?b ?c)) ?a) <=> (< (max ?d (+ ?b ?c)) (max ?b ?a)) if  (< 0 ?c)
(< (+ ?d (max ?c ?b)) ?a) <=> (< (+ ?d (max ?c ?b)) (max ?b ?a)) if  (< 0 ?d)
(< (+ ?d ?c) (+ ?b ?a)) <=> (< (+ ?d ?c) (max ?b (+ ?b ?a))) if  (< 0 ?a)
(< (max ?d ?c) (max ?b (+ ?b ?a))) <=> (< (max ?d ?c) (+ ?b ?a)) if  (< 0 ?a)
(< ?d (+ ?c (max ?b ?a))) <=> (< (max ?d ?c) (+ ?c (max ?b ?a))) if  (< 0 ?a)
(< (+ ?d (max ?c ?b)) ?a) <=> (< (+ ?d (max ?c ?b)) (max ?d ?a)) if  (< 0 ?b)
(< (max ?d ?b) (+ ?c (max ?b ?a))) <=> (< ?d (+ ?c (max ?b ?a))) if  (< 0 ?c)
(< (max ?d ?c) (+ ?c (max ?b ?a))) <=> (< ?d (+ ?c (max ?b ?a))) if  (< 0 ?b)
(< (max ?c ?b) (max ?a (+ ?c ?d))) ==> (< (max ?c ?b) ?a) if (< ?d 0)
(< (max ?c ?b) (max ?a (+ ?b ?d))) ==> (< (max ?c ?b) ?a) if (< ?d 0)
(< (max ?c ?b) (max ?a (+ ?a ?d))) ==> (< (max ?c ?b) ?a) if (< ?d 0)
(< (+ ?c ?b) (max ?a (+ ?a ?d))) ==> (< (+ ?c ?b) ?a) if (< ?d 0)
(< (+ ?b (max ?d ?c)) (+ ?c (+ ?b ?a))) ==> 0 if (< ?a 0)
(< (+ ?d (max ?c ?b)) (max ?c (max ?b ?a))) ==> 1 if (< ?d 0)
(< (max ?d (max ?c ?b)) (max ?b (+ ?b ?a))) ==> 0 if (< ?a 0)
(< (+ ?c (+ ?d ?d)) (max ?c (+ ?b ?a))) ==> 1 if (< ?d 0)
(< (+ ?d (+ ?c ?b)) (+ ?c (max ?b ?a))) ==> 1 if (< ?d 0)
(< (+ ?c (+ ?d ?d)) (max ?c (max ?b ?a))) ==> 1 if (< ?d 0)
(< (+ ?d (+ ?b ?a)) (max ?c (+ ?b ?a))) ==> 1 if (< ?d 0)
(< (max ?d (+ ?b ?c)) (+ ?c (+ ?b ?a))) ==> 0 if (< ?a 0)
(< (max ?c (max ?b ?d)) (max ?c (+ ?b ?a))) ==> 0 if (< ?a 0)
(< (max ?d (max ?c ?b)) (+ ?b (+ ?a ?a))) ==> 0 if (< ?a 0)
(< (+ ?d ?c) (max ?c (max ?b ?a))) ==> 1 if (< ?d 0)
(< (max ?b (max ?d ?c)) (+ ?b ?a)) ==> 0 if (< ?a 0)
(< (+ ?d ?c) (max ?c (+ ?b ?a))) ==> 1 if (< ?d 0)
(< (max ?b (+ ?d ?c)) (+ ?b ?a)) ==> 0 if (< ?a 0)
"#;

#[allow(dead_code)]
fn override_total_rules<L: SynthLanguage>(
    keep_total: &Ruleset<L>,
    keep_cond: &Ruleset<L>,
) -> Ruleset<L> {
    let mut result = Ruleset::default();
    result.extend(keep_total.partition(|r| r.cond.is_none()).0);
    result.extend(keep_cond.partition(|r| r.cond.is_some()).0);
    result
}

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
        }, enumo::{ChompyState, Filter, Metric}, halide::og_recipe, recipe_utils::{
            base_lang, iter_metric, recursive_rules_cond, run_workload, run_workload_internal_llm,
            Lang,
        }, time_fn_call, DeriveType, SynthAnalysis
    };

    use super::*;

    #[test]
    fn mul_div_derive_big_wkld() {
        // let rules = include_str!("big-rules.txt");
    }

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

    // #[test]
    // fn chompy_vs_halide() {
    //     if std::env::var("SKIP_RECIPES").is_ok() {
    //         return;
    //     }

    //     // NOTE: I'll do this later.
    //     let _binding = std::env::var("OUT_DIR").expect("OUT_DIR environment variable not set")
    //         + "/halide-derive.json";

    //     let chompy_rules_txt = include_str!("../chompy-rules.txt");
    //     let mut chompy_rules: Ruleset<Pred> = Ruleset::default();

    //     for line in chompy_rules_txt.lines() {
    //         if line.trim().is_empty() {
    //             continue;
    //         }

    //         let res = Rule::from_string(line.trim());

    //         if let Ok((rule, _)) = res {
    //             if rule.is_valid() {
    //                 chompy_rules.add(rule);
    //             }
    //         }
    //     }

    //     let halide_rules_txt = include_str!("../halide-total.txt");
    //     let mut halide_rules: Ruleset<Pred> = Ruleset::default();
    //     for line in halide_rules_txt.lines() {
    //         if line.trim().is_empty() {
    //             continue;
    //         }

    //         let res = Rule::from_string(line.trim());

    //         if let Ok((rule, _)) = res {
    //             if rule.is_valid() {
    //                 halide_rules.add(rule);
    //             }
    //         }
    //     }

    //     println!("Parsed {} Halide rules", halide_rules.len());
    // }

    #[test]
    // A simple derivability test. How many Caviar rules can Chompy's rulesets derive?
    fn chompy_vs_caviar() {
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

        let implication_rules: ImplicationSet<Pred> =
            pairwise_implication_building(&all_conditions);

        // see how many caviar rules we can derive, given the same
        // total caviar rules.
        let forward_result =
            run_derivability_tests(&chompy_rules, &caviar_rules, &implication_rules);
        // NOTE: cutting this because too expensive.
        // let backward_result =
        //     run_derivability_tests(&caviar_rules, &chompy_rules, &implication_rules);

        let to_json = |result: DerivabilityResult<Pred>| {
            serde_json::json!({
                "can": result.can.iter().map(|r| r.to_string()).collect::<Vec<_>>(),
                "cannot": result.cannot.iter().map(|r| r.to_string()).collect::<Vec<_>>(),
            })
        };

        let to_write = serde_json::json!({
            "forwards": to_json(forward_result),
            // "backwards": to_json(backward_result),
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

    #[test]
    fn test_timeout() {
        let mut rules: Ruleset<Pred> = Ruleset::from_file("/Users/acheung/research/projects/chompy/with-timeout.txt");
        // for line in CHOMPY_RULES.lines() {
        //     let line = line.trim();
        //     if line.is_empty() {
        //         continue;
        //     }

        //     let res = Rule::from_string(line);

        //     if res.is_err() {
        //         panic!("Failed to parse rule: {}", line);
        //     }

        //     let (fw, bw) = res.unwrap();

        //     rules.add(fw);

        //     if let Some(bw) = bw {
        //         rules.add(bw);
        //     }
        // }

        println!("our rules:");
        for r in rules.iter() {
            println!("  {r}");
        }

        let caviar_rules = caviar_rules();

        let mut can: Ruleset<Pred> = Ruleset::default();
        let mut cannot: Ruleset<Pred> = Ruleset::default();


        for c in caviar_rules.iter() {
            if c.cond.is_some() {
                println!("I'm trying to derive: {c}");
                let derive_result = time_fn_call!(
                    format!("can_derive_{}", c.name),
                    rules.can_derive_cond(DeriveType::LhsAndRhs, c, Limits::deriving(), &vec![]));
                if derive_result {
                    can.add(c.clone());
                } else {
                    cannot.add(c.clone());
                }
            }
        }

        let result = DerivabilityResult { can, cannot };

        // write it to derive-with-timeout.json
        let binding = std::env::var("OUT_DIR").expect("OUT_DIR environment variable not set")
            + "/derive-with-timeout.json";

        let out_path: &Path = Path::new(&binding);

        println!("I derived {}", result.can.len());
        println!("I could not derive {}", result.cannot.len());

        let result_json = |result: DerivabilityResult<Pred>| {
            serde_json::json!({
                "can": result.can.iter().map(|r| r.to_string()).collect::<Vec<_>>(),
                "cannot": result.cannot.iter().map(|r| r.to_string()).collect::<Vec<_>>(),
            })
        };

        std::fs::write(out_path, result_json(result).to_string())
            .expect("Failed to write derivability results to file");


    }

            
        
}


