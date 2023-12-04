// Lean compiler output
// Module: LeanCourse.DiffGeom
// Imports: Init Mathlib.Geometry.Manifold.VectorBundle.SmoothSection Mathlib.Geometry.Manifold.VectorBundle.Hom Mathlib.Geometry.Manifold.VectorBundle.Pullback Mathlib.Geometry.Manifold.ContMDiffMFDeriv Mathlib.Geometry.Manifold.Instances.sphere
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Geometry_Manifold_VectorBundle_SmoothSection(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Geometry_Manifold_VectorBundle_Hom(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Geometry_Manifold_VectorBundle_Pullback(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Geometry_Manifold_ContMDiffMFDeriv(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Geometry_Manifold_Instances_sphere(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LeanCourse_DiffGeom(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Geometry_Manifold_VectorBundle_SmoothSection(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Geometry_Manifold_VectorBundle_Hom(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Geometry_Manifold_VectorBundle_Pullback(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Geometry_Manifold_ContMDiffMFDeriv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Geometry_Manifold_Instances_sphere(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
