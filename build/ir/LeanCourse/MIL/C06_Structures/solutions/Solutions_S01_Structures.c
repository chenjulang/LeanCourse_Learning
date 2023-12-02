// Lean compiler output
// Module: LeanCourse.MIL.C06_Structures.solutions.Solutions_S01_Structures
// Imports: Init LeanCourse.Common Mathlib.Algebra.BigOperators.Ring Mathlib.Data.Real.Basic
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
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_900_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_C06S01_StandardSimplex_weightedAverage(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_C06S01_Point_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_C06S01_StandardTwoSimplex_weightedAverage(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Mathlib_Data_Real_Basic_0__Real_one;
LEAN_EXPORT lean_object* l_C06S01_StandardSimplex_weightedAverage___elambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_C06S01_Point_smul(lean_object*, lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1165_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_C06S01_StandardSimplex_weightedAverage___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_C06S01_StandardSimplex_weightedAverage___elambda__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1338_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_C06S01_StandardSimplex_weightedAverage___elambda__1(lean_object*);
LEAN_EXPORT lean_object* l_C06S01_Point_add(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_C06S01_Point_smul(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_inc(x_1);
x_4 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1338_(x_1, x_3);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_1);
x_6 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1338_(x_1, x_5);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1338_(x_1, x_7);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_C06S01_StandardTwoSimplex_weightedAverage(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_inc(x_1);
x_7 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1338_(x_1, x_6);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1165_), 2, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = l___private_Mathlib_Data_Real_Basic_0__Real_one;
x_10 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_900_(x_9, x_8);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_inc(x_10);
x_12 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1338_(x_10, x_11);
x_13 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_900_(x_7, x_12);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_1);
x_15 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1338_(x_1, x_14);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_inc(x_10);
x_17 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1338_(x_10, x_16);
x_18 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_900_(x_15, x_17);
x_19 = lean_ctor_get(x_4, 2);
lean_inc(x_19);
lean_dec(x_4);
x_20 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1338_(x_1, x_19);
x_21 = lean_ctor_get(x_5, 2);
lean_inc(x_21);
lean_dec(x_5);
x_22 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1338_(x_10, x_21);
x_23 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_900_(x_20, x_22);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_23);
return x_24;
}
}
LEAN_EXPORT lean_object* l_C06S01_StandardSimplex_weightedAverage___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_4);
x_5 = lean_apply_1(x_2, x_4);
lean_inc(x_1);
x_6 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1338_(x_1, x_5);
x_7 = lean_alloc_closure((void*)(l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1165_), 2, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l___private_Mathlib_Data_Real_Basic_0__Real_one;
x_9 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_900_(x_8, x_7);
x_10 = lean_apply_1(x_3, x_4);
x_11 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1338_(x_9, x_10);
x_12 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_900_(x_6, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_C06S01_StandardSimplex_weightedAverage___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_C06S01_StandardSimplex_weightedAverage___elambda__1___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_C06S01_StandardSimplex_weightedAverage(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_C06S01_StandardSimplex_weightedAverage___elambda__1___rarg), 4, 3);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_5);
lean_closure_set(x_7, 2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_C06S01_StandardSimplex_weightedAverage___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_C06S01_StandardSimplex_weightedAverage___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_C06S01_StandardSimplex_weightedAverage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_C06S01_StandardSimplex_weightedAverage(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_LeanCourse_Common(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_BigOperators_Ring(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Real_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LeanCourse_MIL_C06__Structures_solutions_Solutions__S01__Structures(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LeanCourse_Common(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_BigOperators_Ring(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Real_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
