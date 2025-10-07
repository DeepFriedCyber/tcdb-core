//! Euler Characteristic Tests
//!
//! Integration tests for Euler characteristic computation.

use tcdb_core::euler::FVector;

#[test]
fn empty_has_chi_zero() {
    let empty = FVector::empty();
    assert_eq!(empty.euler_characteristic(), 0);
}

#[test]
fn point_has_chi_one() {
    let point = FVector::point();
    assert_eq!(point.euler_characteristic(), 1);
}

#[test]
fn interval_has_chi_one() {
    let interval = FVector::interval();
    assert_eq!(interval.euler_characteristic(), 1);
}

#[test]
fn triangle_has_chi_one() {
    let triangle = FVector::triangle();
    assert_eq!(triangle.euler_characteristic(), 1);
}

#[test]
fn tetrahedron_has_chi_one() {
    let tet = FVector::tetrahedron();
    assert_eq!(tet.euler_characteristic(), 1);
}

#[test]
fn chi_additive_triangles() {
    let t1 = FVector::triangle();
    let t2 = FVector::triangle();
    let union = t1.disjoint_union(&t2);
    
    let chi_union = union.euler_characteristic();
    let chi_sum = t1.euler_characteristic() + t2.euler_characteristic();
    
    assert_eq!(chi_union, chi_sum, "χ(A ⊔ B) = χ(A) + χ(B)");
}

#[test]
fn chi_additive_mixed() {
    let point = FVector::point();
    let interval = FVector::interval();
    let union = point.disjoint_union(&interval);
    
    let chi_union = union.euler_characteristic();
    let chi_sum = point.euler_characteristic() + interval.euler_characteristic();
    
    assert_eq!(chi_union, chi_sum);
}

#[test]
fn chi_additive_multiple() {
    let a = FVector::point();
    let b = FVector::interval();
    let c = FVector::triangle();
    
    let union = a.disjoint_union(&b).disjoint_union(&c);
    
    let chi_union = union.euler_characteristic();
    let chi_sum = a.euler_characteristic() + b.euler_characteristic() + c.euler_characteristic();
    
    assert_eq!(chi_union, chi_sum);
}

#[test]
fn disjoint_union_commutative() {
    let a = FVector::triangle();
    let b = FVector::interval();
    
    let ab = a.disjoint_union(&b);
    let ba = b.disjoint_union(&a);
    
    assert_eq!(ab.faces, ba.faces, "A ⊔ B = B ⊔ A");
}

#[test]
fn disjoint_union_associative() {
    let a = FVector::point();
    let b = FVector::interval();
    let c = FVector::triangle();
    
    let ab_c = a.disjoint_union(&b).disjoint_union(&c);
    let a_bc = a.disjoint_union(&b.disjoint_union(&c));
    
    assert_eq!(ab_c.faces, a_bc.faces, "(A ⊔ B) ⊔ C = A ⊔ (B ⊔ C)");
}

#[test]
fn disjoint_union_identity() {
    let a = FVector::triangle();
    let empty = FVector::empty();
    
    let union = a.disjoint_union(&empty);
    
    // Should have same Euler characteristic
    assert_eq!(union.euler_characteristic(), a.euler_characteristic());
}

#[test]
fn multiple_points() {
    let point = FVector::point();
    
    // 10 points
    let mut result = FVector::empty();
    for _ in 0..10 {
        result = result.disjoint_union(&point);
    }
    
    assert_eq!(result.euler_characteristic(), 10);
}

#[test]
fn multiple_triangles() {
    let triangle = FVector::triangle();
    
    // 5 triangles
    let mut result = FVector::empty();
    for _ in 0..5 {
        result = result.disjoint_union(&triangle);
    }
    
    assert_eq!(result.euler_characteristic(), 5);
}

#[test]
fn face_counts_correct() {
    let triangle = FVector::triangle();
    
    assert_eq!(triangle.get_face_count(0), 3, "3 vertices");
    assert_eq!(triangle.get_face_count(1), 3, "3 edges");
    assert_eq!(triangle.get_face_count(2), 1, "1 face");
    assert_eq!(triangle.get_face_count(3), 0, "0 solids");
}

#[test]
fn max_dimension_correct() {
    assert_eq!(FVector::empty().max_dimension(), 0);
    assert_eq!(FVector::point().max_dimension(), 0);
    assert_eq!(FVector::interval().max_dimension(), 1);
    assert_eq!(FVector::triangle().max_dimension(), 2);
    assert_eq!(FVector::tetrahedron().max_dimension(), 3);
}

#[test]
fn custom_fvector() {
    // Custom complex: 5 vertices, 7 edges, 3 faces
    let custom = FVector::new(vec![5, 7, 3]);
    
    // χ = 5 - 7 + 3 = 1
    assert_eq!(custom.euler_characteristic(), 1);
}

#[test]
fn sphere_approximation() {
    // Sphere (octahedron): 6 vertices, 12 edges, 8 faces
    let sphere = FVector::new(vec![6, 12, 8]);
    
    // χ = 6 - 12 + 8 = 2
    assert_eq!(sphere.euler_characteristic(), 2);
}

#[test]
fn torus_approximation() {
    // Torus: 9 vertices, 27 edges, 18 faces
    let torus = FVector::new(vec![9, 27, 18]);
    
    // χ = 9 - 27 + 18 = 0
    assert_eq!(torus.euler_characteristic(), 0);
}

#[test]
fn projective_plane_approximation() {
    // Projective plane: 6 vertices, 15 edges, 10 faces
    let proj_plane = FVector::new(vec![6, 15, 10]);
    
    // χ = 6 - 15 + 10 = 1
    assert_eq!(proj_plane.euler_characteristic(), 1);
}

#[test]
fn klein_bottle_approximation() {
    // Klein bottle: 8 vertices, 24 edges, 16 faces
    let klein = FVector::new(vec![8, 24, 16]);
    
    // χ = 8 - 24 + 16 = 0
    assert_eq!(klein.euler_characteristic(), 0);
}

#[test]
fn two_spheres() {
    let sphere = FVector::new(vec![6, 12, 8]);
    let two_spheres = sphere.disjoint_union(&sphere);
    
    // χ(S² ⊔ S²) = χ(S²) + χ(S²) = 2 + 2 = 4
    assert_eq!(two_spheres.euler_characteristic(), 4);
}

#[test]
fn sphere_and_torus() {
    let sphere = FVector::new(vec![6, 12, 8]);
    let torus = FVector::new(vec![9, 27, 18]);
    let union = sphere.disjoint_union(&torus);
    
    // χ(S² ⊔ T²) = χ(S²) + χ(T²) = 2 + 0 = 2
    assert_eq!(union.euler_characteristic(), 2);
}

#[test]
fn serialization_roundtrip() {
    let triangle = FVector::triangle();
    
    // Serialize to JSON
    let json = serde_json::to_string(&triangle).unwrap();
    
    // Deserialize back
    let triangle2: FVector = serde_json::from_str(&json).unwrap();
    
    assert_eq!(triangle, triangle2);
    assert_eq!(triangle.euler_characteristic(), triangle2.euler_characteristic());
}

#[test]
fn zero_dimensional_complex() {
    // Just vertices, no edges
    let vertices = FVector::new(vec![5]);
    
    // χ = 5
    assert_eq!(vertices.euler_characteristic(), 5);
}

#[test]
fn one_dimensional_complex() {
    // Graph: 4 vertices, 3 edges (tree)
    let tree = FVector::new(vec![4, 3]);
    
    // χ = 4 - 3 = 1
    assert_eq!(tree.euler_characteristic(), 1);
}

#[test]
fn cycle_graph() {
    // Cycle: 4 vertices, 4 edges
    let cycle = FVector::new(vec![4, 4]);
    
    // χ = 4 - 4 = 0
    assert_eq!(cycle.euler_characteristic(), 0);
}

#[test]
fn complete_graph_k4() {
    // K₄: 4 vertices, 6 edges
    let k4 = FVector::new(vec![4, 6]);
    
    // χ = 4 - 6 = -2
    assert_eq!(k4.euler_characteristic(), -2);
}

#[test]
fn high_dimensional_simplex() {
    // 4-simplex: 5 vertices, 10 edges, 10 faces, 5 solids, 1 4-simplex
    let simplex_4 = FVector::new(vec![5, 10, 10, 5, 1]);
    
    // χ = 5 - 10 + 10 - 5 + 1 = 1
    assert_eq!(simplex_4.euler_characteristic(), 1);
}

#[test]
fn alternating_sum_property() {
    // Verify alternating sum for custom complex
    let fvec = FVector::new(vec![10, 20, 15, 5]);
    
    let chi = fvec.euler_characteristic();
    let expected = 10 - 20 + 15 - 5;
    
    assert_eq!(chi, expected);
}

#[test]
fn empty_union_empty() {
    let e1 = FVector::empty();
    let e2 = FVector::empty();
    let union = e1.disjoint_union(&e2);
    
    assert_eq!(union.euler_characteristic(), 0);
}

#[test]
fn large_disjoint_union() {
    let point = FVector::point();
    
    // 100 points
    let mut result = FVector::empty();
    for _ in 0..100 {
        result = result.disjoint_union(&point);
    }
    
    assert_eq!(result.euler_characteristic(), 100);
}

#[test]
fn mixed_dimensions() {
    let a = FVector::new(vec![3, 2]);      // 3 vertices, 2 edges
    let b = FVector::new(vec![2, 3, 1]);   // 2 vertices, 3 edges, 1 face
    
    let union = a.disjoint_union(&b);
    
    // Union: 5 vertices, 5 edges, 1 face
    assert_eq!(union.get_face_count(0), 5);
    assert_eq!(union.get_face_count(1), 5);
    assert_eq!(union.get_face_count(2), 1);
    
    // χ = 5 - 5 + 1 = 1
    assert_eq!(union.euler_characteristic(), 1);
}

#[test]
fn chi_respects_commutativity() {
    let a = FVector::triangle();
    let b = FVector::interval();
    
    let ab = a.disjoint_union(&b);
    let ba = b.disjoint_union(&a);
    
    assert_eq!(ab.euler_characteristic(), ba.euler_characteristic());
}

#[test]
fn chi_respects_associativity() {
    let a = FVector::point();
    let b = FVector::interval();
    let c = FVector::triangle();
    
    let ab_c = a.disjoint_union(&b).disjoint_union(&c);
    let a_bc = a.disjoint_union(&b.disjoint_union(&c));
    
    assert_eq!(ab_c.euler_characteristic(), a_bc.euler_characteristic());
}

