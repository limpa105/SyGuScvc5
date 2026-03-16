(set-logic ALL)

;; ------------------------------------------------------------------------------------
;; ------------------------------- Basic Data Types -----------------------------------
;; ------------------------------------------------------------------------------------

;; Define a 3D Point
(declare-datatype Point3D 
  ((mk-point3d (px Real) (py Real) (pz Real)))
)

;; A Geometry consists of three disjoint regions: Interior, Boundary, Exterior
(declare-datatype Geometry (
  (mk-geometry 
    (I (Set Point3D)) ;; Interior
    (B (Set Point3D)) ;; Boundary
    (E (Set Point3D)) ;; Exterior
  )
))



;; Finite Universe of all points
(declare-var U (Set Point3D))




;; ------------------------------------------------------------------------------------
;; ---------------------------- Spatial Predicates ------------------------------------
;; ------------------------------------------------------------------------------------

(define-fun Covers ((g1 Geometry) (g2 Geometry)) Bool
  (and
    (or
      (not (= (set.inter (I g1) (I g2)) (as set.empty (Set Point3D))))
      (not (= (set.inter (I g1) (B g2)) (as set.empty (Set Point3D))))
      (not (= (set.inter (B g1) (I g2)) (as set.empty (Set Point3D))))
      (not (= (set.inter (B g1) (B g2)) (as set.empty (Set Point3D))))
    )
    (= (set.inter (E g1) (I g2)) (as set.empty (Set Point3D)))
    (= (set.inter (E g1) (B g2)) (as set.empty (Set Point3D)))
    (=> (not (= (set.inter (I g1) (I g2)) (as set.empty (Set Point3D)))) (= (set.inter (I g2) (I g1)) (I g2))
  ))
)

;; g1 is CoveredBy g2 if g2 Covers g1 
(define-fun CoveredBy ((g1 Geometry) (g2 Geometry)) Bool
  (Covers g2 g1)
)

;; g1 Contains g2 if:
;;   - g1’s Interior overlaps g2’s Interior
;;   - g2 has no Interior/Boundary points in g1’s Exterior
(define-fun Contains ((g1 Geometry) (g2 Geometry)) Bool
  (and
    (not (= (set.inter (I g1) (I g2)) (as set.empty (Set Point3D))))
    (= (set.inter (E g1) (I g2)) (as set.empty (Set Point3D)))
    (= (set.inter (E g1) (B g2)) (as set.empty (Set Point3D)))
    (= (set.inter (I g2) (I g1)) (I g2)))
  )

;; g1 is Within g2 if g2 Contains g1
(define-fun Within ((g1 Geometry) (g2 Geometry)) Bool
  (Contains g2 g1)
)

;; g1 and g2 are Disjoint if their Interiors and Boundaries do not overlap
(define-fun Disjoint ((g1 Geometry) (g2 Geometry)) Bool
  (and
    (= (set.inter (I g1) (I g2)) (as set.empty (Set Point3D)))
    (= (set.inter (I g1) (B g2)) (as set.empty (Set Point3D)))
    (= (set.inter (B g1) (I g2)) (as set.empty (Set Point3D)))
    (= (set.inter (B g1) (B g2)) (as set.empty (Set Point3D)))
  )
)

;; g1 Intersects g2 if they are not disjoint
(define-fun Intersects ((g1 Geometry) (g2 Geometry)) Bool
  (not (Disjoint g1 g2))
)

;; g1 and g2 are Equal if they share exactly the same points
(define-fun Equals ((g1 Geometry) (g2 Geometry)) Bool
  (and
    (not (= (set.inter (I g1) (I g2)) (as set.empty (Set Point3D))))
    (= (set.inter (I g1) (E g2)) (as set.empty (Set Point3D)))
    (= (set.inter (B g1) (E g2)) (as set.empty (Set Point3D)))
    (= (set.inter (E g1) (I g2)) (as set.empty (Set Point3D)))
    (= (set.inter (E g1) (B g2)) (as set.empty (Set Point3D)))
    (= (set.inter (I g2) (I g1)) (I g2))
    (= (set.inter (I g2) (I g1)) (I g1))
  )
)

;; g1 Touches g2 if they share only boundary points
(define-fun Touches ((g1 Geometry) (g2 Geometry)) Bool
  (and
    (= (set.inter (I g1) (I g2)) (as set.empty (Set Point3D)))
    (not (= (set.inter (I g1) (B g2)) (as set.empty (Set Point3D))))
    (not (= (set.inter (B g1) (I g2)) (as set.empty (Set Point3D))))
    (not (= (set.inter (B g1) (B g2)) (as set.empty (Set Point3D))))
  )
)



;; ------------------------------------------------------------------------------------
;; ------------------------------- Synthesis Setup ------------------------------------
;; ------------------------------------------------------------------------------------

;; Synthesizing a Boolean predicate over geometries
(synth-fun pred_f ((x Geometry) (y Geometry)) Bool
  ;; F = CNF formula (AND of clauses)
  ;; C = clause (OR of atoms)
  ;; A = atom
  ((F Bool) (C Bool) (A Bool))
  (
    ;; CNF formula
    (F Bool (
      C
      (and F F)
    ))

    ;; Clause
    (C Bool (
       A
      (not A)
      (or C C)
    ))

    ;; Atoms
    (A Bool (
      true
      false
      (Contains x y)
      (Covers x y)
      (CoveredBy x y)
      (Touches x y)
      (Within x y)
      (Equals x y)
      (Disjoint x y)
      (Intersects x y)

    ))
  )
)




;; ------------------------------------------------------------------------------------
;; ------------------------------- Problem Setup --------------------------------------
;; ------------------------------------------------------------------------------------

;; Declare variables
(declare-var a Geometry)
(declare-var b Geometry)
(declare-var bounding_volume_a Geometry)
(declare-var bounding_volume_b Geometry)


;; ------------------------------------------------------------------------------------
;; ------------------------------- Geometry Validity ----------------------------------
;; ------------------------------------------------------------------------------------

;; Valid geometry constraints:
;;   - Interior ∪ Boundary ∪ Exterior = Universe
;;   - Regions are pairwise disjoint
;;   - Interior is non-empty
(define-fun is_valid_geometry ((a Geometry)) Bool
  (and 
    (= (set.union (I a) (set.union (B a) (E a))) U) 
    (= (set.inter (I a) (B a)) (as set.empty (Set Point3D)))
    (= (set.inter (E a) (B a)) (as set.empty (Set Point3D)))
    (= (set.inter (E a) (I a)) (as set.empty (Set Point3D)))
    (not (= (I a) (as set.empty (Set Point3D))))
  )
)

(define-fun is_bounding_volume ((bounding_volume_g Geometry) (g Geometry)) Bool
  (and (Covers bounding_volume_g g)
  (= (set.inter (I g) (I bounding_volume_g)) (I g))
  (= (set.inter (B g) (B bounding_volume_g)) (B g)))
)

;; ------------------------------------------------------------------------------------
;; ------------------------------- Synthesis Setup  ----------------------------------------
;; ------------------------------------------------------------------------------------


(assume (and 
        (is_valid_geometry a)
        (is_valid_geometry b)
        (is_valid_geometry bounding_volume_a)
        (is_valid_geometry bounding_volume_b)
        (is_bounding_volume bounding_volume_b b)
        (is_bounding_volume bounding_volume_a a)
        )
)






;; ------------------------------------------------------------------------------------
;; ------------------------------- Synthesis Check ------------------------------------
;; ------------------------------------------------------------------------------------



(constraint (=> (pred_f bounding_volume_a bounding_volume_b) (Contains a b)))
(check-synth)
(check-synth-next)
(check-synth-next)
(check-synth-next)
(check-synth-next)
(check-synth-next)
(check-synth-next)
(check-synth-next)
(check-synth-next)
