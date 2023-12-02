// Lean compiler output
// Module: LeanCourse.MIL.C06_Structures.solutions.Solutions_S02_Algebraic_Structures
// Imports: Init LeanCourse.Common Mathlib.Data.Real.Basic
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
extern lean_object* l___private_Mathlib_Data_Real_Basic_0__Real_zero;
LEAN_EXPORT lean_object* l_C06S02_Point_addGroupPoint;
LEAN_EXPORT lean_object* l_C06S02_Point_add(lean_object*, lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_900_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_C06S02_hasZeroAddGroup_u2082(lean_object*);
LEAN_EXPORT lean_object* l_C06S02_Point_zero;
LEAN_EXPORT lean_object* l_C06S02_hasNegAddGroup_u2082(lean_object*);
static lean_object* l_C06S02_Point_addGroupPoint___closed__2;
LEAN_EXPORT lean_object* l_C06S02_hasAddAddGroup_u2082___rarg(lean_object*);
LEAN_EXPORT lean_object* l_C06S02_hasAddAddGroup_u2082(lean_object*);
static lean_object* l_C06S02_Point_addGroupPoint___closed__3;
static lean_object* l_C06S02_instAddGroup_u2082Point___closed__1;
LEAN_EXPORT lean_object* l_C06S02_hasAddAddGroup_u2082___rarg___boxed(lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1165_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_C06S02_hasNegAddGroup_u2082___rarg(lean_object*);
static lean_object* l_C06S02_Point_addGroupPoint___closed__1;
LEAN_EXPORT lean_object* l_C06S02_Point_neg(lean_object*);
LEAN_EXPORT lean_object* l_C06S02_hasZeroAddGroup_u2082___rarg(lean_object*);
LEAN_EXPORT lean_object* l_C06S02_hasNegAddGroup_u2082___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_C06S02_hasZeroAddGroup_u2082___rarg___boxed(lean_object*);
static lean_object* l_C06S02_Point_zero___closed__1;
LEAN_EXPORT lean_object* l_C06S02_instAddGroup_u2082Point;
LEAN_EXPORT lean_object* l_C06S02_Point_add(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_900_(x_3, x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_900_(x_6, x_7);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_900_(x_9, x_10);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_C06S02_Point_neg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_closure((void*)(l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1165_), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1165_), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_closure((void*)(l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1165_), 2, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
}
static lean_object* _init_l_C06S02_Point_zero___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Mathlib_Data_Real_Basic_0__Real_zero;
x_2 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_C06S02_Point_zero() {
_start:
{
lean_object* x_1; 
x_1 = l_C06S02_Point_zero___closed__1;
return x_1;
}
}
static lean_object* _init_l_C06S02_Point_addGroupPoint___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_C06S02_Point_add), 2, 0);
return x_1;
}
}
static lean_object* _init_l_C06S02_Point_addGroupPoint___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_C06S02_Point_neg), 1, 0);
return x_1;
}
}
static lean_object* _init_l_C06S02_Point_addGroupPoint___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_C06S02_Point_addGroupPoint___closed__1;
x_2 = l_C06S02_Point_zero;
x_3 = l_C06S02_Point_addGroupPoint___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_C06S02_Point_addGroupPoint() {
_start:
{
lean_object* x_1; 
x_1 = l_C06S02_Point_addGroupPoint___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_C06S02_hasAddAddGroup_u2082___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_C06S02_hasAddAddGroup_u2082(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_C06S02_hasAddAddGroup_u2082___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_C06S02_hasAddAddGroup_u2082___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_C06S02_hasAddAddGroup_u2082___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_C06S02_hasZeroAddGroup_u2082___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_C06S02_hasZeroAddGroup_u2082(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_C06S02_hasZeroAddGroup_u2082___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_C06S02_hasZeroAddGroup_u2082___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_C06S02_hasZeroAddGroup_u2082___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_C06S02_hasNegAddGroup_u2082___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_C06S02_hasNegAddGroup_u2082(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_C06S02_hasNegAddGroup_u2082___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_C06S02_hasNegAddGroup_u2082___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_C06S02_hasNegAddGroup_u2082___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_C06S02_instAddGroup_u2082Point___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_C06S02_Point_addGroupPoint___closed__1;
x_2 = l_C06S02_Point_zero;
x_3 = l_C06S02_Point_addGroupPoint___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_C06S02_instAddGroup_u2082Point() {
_start:
{
lean_object* x_1; 
x_1 = l_C06S02_instAddGroup_u2082Point___closed__1;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_LeanCourse_Common(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Real_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LeanCourse_MIL_C06__Structures_solutions_Solutions__S02__Algebraic__Structures(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LeanCourse_Common(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Real_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_C06S02_Point_zero___closed__1 = _init_l_C06S02_Point_zero___closed__1();
lean_mark_persistent(l_C06S02_Point_zero___closed__1);
l_C06S02_Point_zero = _init_l_C06S02_Point_zero();
lean_mark_persistent(l_C06S02_Point_zero);
l_C06S02_Point_addGroupPoint___closed__1 = _init_l_C06S02_Point_addGroupPoint___closed__1();
lean_mark_persistent(l_C06S02_Point_addGroupPoint___closed__1);
l_C06S02_Point_addGroupPoint___closed__2 = _init_l_C06S02_Point_addGroupPoint___closed__2();
lean_mark_persistent(l_C06S02_Point_addGroupPoint___closed__2);
l_C06S02_Point_addGroupPoint___closed__3 = _init_l_C06S02_Point_addGroupPoint___closed__3();
lean_mark_persistent(l_C06S02_Point_addGroupPoint___closed__3);
l_C06S02_Point_addGroupPoint = _init_l_C06S02_Point_addGroupPoint();
lean_mark_persistent(l_C06S02_Point_addGroupPoint);
l_C06S02_instAddGroup_u2082Point___closed__1 = _init_l_C06S02_instAddGroup_u2082Point___closed__1();
lean_mark_persistent(l_C06S02_instAddGroup_u2082Point___closed__1);
l_C06S02_instAddGroup_u2082Point = _init_l_C06S02_instAddGroup_u2082Point();
lean_mark_persistent(l_C06S02_instAddGroup_u2082Point);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
