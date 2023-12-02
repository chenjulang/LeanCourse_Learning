// Lean compiler output
// Module: LeanCourse.MIL.C05_Elementary_Number_Theory.solutions.Solutions_S02_Induction_and_Recursion
// Imports: Init Mathlib.Data.Nat.GCD.Basic Mathlib.Algebra.BigOperators.Basic LeanCourse.Common
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
LEAN_EXPORT lean_object* l___private_LeanCourse_MIL_C05__Elementary__Number__Theory_solutions_Solutions__S02__Induction__and__Recursion_0__MyNat_add_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l___private_LeanCourse_MIL_C05__Elementary__Number__Theory_solutions_Solutions__S02__Induction__and__Recursion_0__fac_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MyNat_add___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_fac(lean_object*);
LEAN_EXPORT lean_object* l_MyNat_mul___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanCourse_MIL_C05__Elementary__Number__Theory_solutions_Solutions__S02__Induction__and__Recursion_0__MyNat_add_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MyNat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MyNat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_fac___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_LeanCourse_MIL_C05__Elementary__Number__Theory_solutions_Solutions__S02__Induction__and__Recursion_0__fac_match__1_splitter(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanCourse_MIL_C05__Elementary__Number__Theory_solutions_Solutions__S02__Induction__and__Recursion_0__fac_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_fac(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_1, x_4);
x_6 = lean_nat_add(x_5, x_4);
x_7 = l_fac(x_5);
lean_dec(x_5);
x_8 = lean_nat_mul(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(1u);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_fac___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_fac(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_LeanCourse_MIL_C05__Elementary__Number__Theory_solutions_Solutions__S02__Induction__and__Recursion_0__fac_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
else
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanCourse_MIL_C05__Elementary__Number__Theory_solutions_Solutions__S02__Induction__and__Recursion_0__fac_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_LeanCourse_MIL_C05__Elementary__Number__Theory_solutions_Solutions__S02__Induction__and__Recursion_0__fac_match__1_splitter___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_LeanCourse_MIL_C05__Elementary__Number__Theory_solutions_Solutions__S02__Induction__and__Recursion_0__fac_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_LeanCourse_MIL_C05__Elementary__Number__Theory_solutions_Solutions__S02__Induction__and__Recursion_0__fac_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_MyNat_add(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_MyNat_add(x_1, x_4);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_MyNat_add(x_1, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_MyNat_add___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_MyNat_add(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_MyNat_mul(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_1);
x_5 = l_MyNat_mul(x_1, x_4);
x_6 = l_MyNat_add(x_5, x_1);
lean_dec(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_MyNat_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_MyNat_mul(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_LeanCourse_MIL_C05__Elementary__Number__Theory_solutions_Solutions__S02__Induction__and__Recursion_0__MyNat_add_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_apply_1(x_3, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_apply_2(x_4, x_1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_LeanCourse_MIL_C05__Elementary__Number__Theory_solutions_Solutions__S02__Induction__and__Recursion_0__MyNat_add_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_LeanCourse_MIL_C05__Elementary__Number__Theory_solutions_Solutions__S02__Induction__and__Recursion_0__MyNat_add_match__1_splitter___rarg), 4, 0);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Nat_GCD_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_BigOperators_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_LeanCourse_Common(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LeanCourse_MIL_C05__Elementary__Number__Theory_solutions_Solutions__S02__Induction__and__Recursion(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Nat_GCD_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_BigOperators_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LeanCourse_Common(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
