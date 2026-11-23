#[path="reference_canonical.rs"] mod canonical;
#[path="reference_resolve.rs"] mod resolve;
#[path="reference_parse.rs"] mod parse;
#[path="reference_module.rs"] mod module;
include!("generated_fixtures.rs");

#[test]
fn upstream_only_resource_and_collection_boundaries() {
    use canonical::RhoValue;
    use module::{CanonicalModuleValue, CanonicalModuleExport, CanonicalModuleDependency};
    use resolve::ModuleRef;
    let mut value = RhoValue::Nil;
    for _ in 0..260 { value = RhoValue::List(vec![value]); }
    let deep = CanonicalModuleValue { name: "Deep".into(), dependencies: vec![],
        exports: vec![CanonicalModuleExport { name: "Expr".into(), spec: value }] };
    assert!(CanonicalModuleValue::from_rho_value(&deep.to_rho_value()).is_err());
    let exports = (0..1025).map(|n| CanonicalModuleExport { name: format!("Expr{n}"),
        spec: RhoValue::Nil }).collect();
    let wide = CanonicalModuleValue { name: "Wide".into(), dependencies: vec![], exports };
    assert!(CanonicalModuleValue::from_rho_value(&wide.to_rho_value()).is_err());
    let dependencies = (0..257).map(|n| CanonicalModuleDependency {
        reference: ModuleRef::Registry(format!("rho:base{n}")), commitment: [66;32] }).collect();
    let dependencies_wide = CanonicalModuleValue { name: "WideDependencies".into(), dependencies,
        exports: vec![CanonicalModuleExport { name: "Expr".into(), spec: RhoValue::Nil }] };
    assert!(CanonicalModuleValue::from_rho_value(&dependencies_wide.to_rho_value()).is_err());
}
