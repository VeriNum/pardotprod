From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.10".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "32sse2".
  Definition abi := "standard".
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "dotprod.c".
  Definition normalized := true.
End Info.

Definition _N : ident := $"N".
Definition _R : ident := $"R".
Definition _REPEAT : ident := $"REPEAT".
Definition _T : ident := $"T".
Definition __155 : ident := $"_155".
Definition __156 : ident := $"_156".
Definition __229 : ident := $"_229".
Definition __230 : ident := $"_230".
Definition __231 : ident := $"_231".
Definition __Bigint : ident := $"_Bigint".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___cleanup : ident := $"__cleanup".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition ___count : ident := $"__count".
Definition ___getreent : ident := $"__getreent".
Definition ___locale_t : ident := $"__locale_t".
Definition ___sFILE64 : ident := $"__sFILE64".
Definition ___sbuf : ident := $"__sbuf".
Definition ___sdidinit : ident := $"__sdidinit".
Definition ___sf : ident := $"__sf".
Definition ___sglue : ident := $"__sglue".
Definition ___stringlit_1 : ident := $"__stringlit_1".
Definition ___stringlit_2 : ident := $"__stringlit_2".
Definition ___tm : ident := $"__tm".
Definition ___tm_hour : ident := $"__tm_hour".
Definition ___tm_isdst : ident := $"__tm_isdst".
Definition ___tm_mday : ident := $"__tm_mday".
Definition ___tm_min : ident := $"__tm_min".
Definition ___tm_mon : ident := $"__tm_mon".
Definition ___tm_sec : ident := $"__tm_sec".
Definition ___tm_wday : ident := $"__tm_wday".
Definition ___tm_yday : ident := $"__tm_yday".
Definition ___tm_year : ident := $"__tm_year".
Definition ___value : ident := $"__value".
Definition ___wch : ident := $"__wch".
Definition ___wchb : ident := $"__wchb".
Definition __add : ident := $"_add".
Definition __asctime_buf : ident := $"_asctime_buf".
Definition __atexit : ident := $"_atexit".
Definition __atexit0 : ident := $"_atexit0".
Definition __base : ident := $"_base".
Definition __bf : ident := $"_bf".
Definition __blksize : ident := $"_blksize".
Definition __close : ident := $"_close".
Definition __cookie : ident := $"_cookie".
Definition __cvtbuf : ident := $"_cvtbuf".
Definition __cvtlen : ident := $"_cvtlen".
Definition __data : ident := $"_data".
Definition __dso_handle : ident := $"_dso_handle".
Definition __emergency : ident := $"_emergency".
Definition __errno : ident := $"_errno".
Definition __file : ident := $"_file".
Definition __flags : ident := $"_flags".
Definition __flags2 : ident := $"_flags2".
Definition __fnargs : ident := $"_fnargs".
Definition __fns : ident := $"_fns".
Definition __fntypes : ident := $"_fntypes".
Definition __freelist : ident := $"_freelist".
Definition __gamma_signgam : ident := $"_gamma_signgam".
Definition __getdate_err : ident := $"_getdate_err".
Definition __glue : ident := $"_glue".
Definition __h_errno : ident := $"_h_errno".
Definition __inc : ident := $"_inc".
Definition __ind : ident := $"_ind".
Definition __iobs : ident := $"_iobs".
Definition __is_cxa : ident := $"_is_cxa".
Definition __k : ident := $"_k".
Definition __l64a_buf : ident := $"_l64a_buf".
Definition __lb : ident := $"_lb".
Definition __lbfsize : ident := $"_lbfsize".
Definition __locale : ident := $"_locale".
Definition __localtime_buf : ident := $"_localtime_buf".
Definition __lock : ident := $"_lock".
Definition __maxwds : ident := $"_maxwds".
Definition __mblen_state : ident := $"_mblen_state".
Definition __mbrlen_state : ident := $"_mbrlen_state".
Definition __mbrtowc_state : ident := $"_mbrtowc_state".
Definition __mbsrtowcs_state : ident := $"_mbsrtowcs_state".
Definition __mbstate : ident := $"_mbstate".
Definition __mbtowc_state : ident := $"_mbtowc_state".
Definition __mult : ident := $"_mult".
Definition __nbuf : ident := $"_nbuf".
Definition __new : ident := $"_new".
Definition __next : ident := $"_next".
Definition __nextf : ident := $"_nextf".
Definition __niobs : ident := $"_niobs".
Definition __nmalloc : ident := $"_nmalloc".
Definition __offset : ident := $"_offset".
Definition __on_exit_args : ident := $"_on_exit_args".
Definition __p : ident := $"_p".
Definition __p5s : ident := $"_p5s".
Definition __r : ident := $"_r".
Definition __r48 : ident := $"_r48".
Definition __rand48 : ident := $"_rand48".
Definition __rand_next : ident := $"_rand_next".
Definition __read : ident := $"_read".
Definition __reent : ident := $"_reent".
Definition __result : ident := $"_result".
Definition __result_k : ident := $"_result_k".
Definition __seed : ident := $"_seed".
Definition __seek : ident := $"_seek".
Definition __seek64 : ident := $"_seek64".
Definition __sig_func : ident := $"_sig_func".
Definition __sign : ident := $"_sign".
Definition __signal_buf : ident := $"_signal_buf".
Definition __size : ident := $"_size".
Definition __stderr : ident := $"_stderr".
Definition __stdin : ident := $"_stdin".
Definition __stdout : ident := $"_stdout".
Definition __strtok_last : ident := $"_strtok_last".
Definition __ub : ident := $"_ub".
Definition __ubuf : ident := $"_ubuf".
Definition __unspecified_locale_info : ident := $"_unspecified_locale_info".
Definition __unused : ident := $"_unused".
Definition __unused_rand : ident := $"_unused_rand".
Definition __up : ident := $"_up".
Definition __ur : ident := $"_ur".
Definition __w : ident := $"_w".
Definition __wcrtomb_state : ident := $"_wcrtomb_state".
Definition __wcsrtombs_state : ident := $"_wcsrtombs_state".
Definition __wctomb_state : ident := $"_wctomb_state".
Definition __wds : ident := $"_wds".
Definition __write : ident := $"_write".
Definition __x : ident := $"_x".
Definition _acquire : ident := $"acquire".
Definition _argc : ident := $"argc".
Definition _argv : ident := $"argv".
Definition _atoi : ident := $"atoi".
Definition _atom_int : ident := $"atom_int".
Definition _closure : ident := $"closure".
Definition _d : ident := $"d".
Definition _delta : ident := $"delta".
Definition _delta_next : ident := $"delta_next".
Definition _delta_next__1 : ident := $"delta_next__1".
Definition _do_tasks : ident := $"do_tasks".
Definition _dotprod : ident := $"dotprod".
Definition _dotprod_task : ident := $"dotprod_task".
Definition _dotprod_worker : ident := $"dotprod_worker".
Definition _dtasks : ident := $"dtasks".
Definition _exit : ident := $"exit".
Definition _fprintf : ident := $"fprintf".
Definition _freelock : ident := $"freelock".
Definition _goal : ident := $"goal".
Definition _i : ident := $"i".
Definition _initialize_task : ident := $"initialize_task".
Definition _j : ident := $"j".
Definition _main : ident := $"main".
Definition _make_dotprod_tasks : ident := $"make_dotprod_tasks".
Definition _make_tasks : ident := $"make_tasks".
Definition _makelock : ident := $"makelock".
Definition _malloc : ident := $"malloc".
Definition _n : ident := $"n".
Definition _num_threads : ident := $"num_threads".
Definition _placeholder : ident := $"placeholder".
Definition _printf : ident := $"printf".
Definition _release : ident := $"release".
Definition _result : ident := $"result".
Definition _spawn : ident := $"spawn".
Definition _t : ident := $"t".
Definition _task : ident := $"task".
Definition _tasks : ident := $"tasks".
Definition _test : ident := $"test".
Definition _vec1 : ident := $"vec1".
Definition _vec2 : ident := $"vec2".
Definition _w : ident := $"w".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.

Definition v_tasks := {|
  gvar_info := (tptr (Tstruct _task noattr));
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_num_threads := {|
  gvar_info := tuint;
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_dtasks := {|
  gvar_info := (tptr (Tstruct _dotprod_task noattr));
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_dotprod_worker := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_closure, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_w, (tptr (Tstruct _dotprod_task noattr))) ::
               (_result, tdouble) :: (_n, tuint) ::
               (_vec1, (tptr tdouble)) :: (_vec2, (tptr tdouble)) ::
               (_i, tuint) :: (_t'2, tdouble) :: (_t'1, tdouble) :: nil);
  fn_body :=
(Ssequence
  (Sset _w
    (Ecast (Etempvar _closure (tptr tvoid))
      (tptr (Tstruct _dotprod_task noattr))))
  (Ssequence
    (Sset _result (Econst_float (Float.of_bits (Int64.repr 0)) tdouble))
    (Ssequence
      (Sset _n
        (Efield
          (Ederef (Etempvar _w (tptr (Tstruct _dotprod_task noattr)))
            (Tstruct _dotprod_task noattr)) _n tuint))
      (Ssequence
        (Sset _vec1
          (Efield
            (Ederef (Etempvar _w (tptr (Tstruct _dotprod_task noattr)))
              (Tstruct _dotprod_task noattr)) _vec1 (tptr tdouble)))
        (Ssequence
          (Sset _vec2
            (Efield
              (Ederef (Etempvar _w (tptr (Tstruct _dotprod_task noattr)))
                (Tstruct _dotprod_task noattr)) _vec2 (tptr tdouble)))
          (Ssequence
            (Ssequence
              (Sset _i (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                                 (Etempvar _n tuint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sset _t'1
                      (Ederef
                        (Ebinop Oadd (Etempvar _vec1 (tptr tdouble))
                          (Etempvar _i tuint) (tptr tdouble)) tdouble))
                    (Ssequence
                      (Sset _t'2
                        (Ederef
                          (Ebinop Oadd (Etempvar _vec2 (tptr tdouble))
                            (Etempvar _i tuint) (tptr tdouble)) tdouble))
                      (Sset _result
                        (Ebinop Oadd (Etempvar _result tdouble)
                          (Ebinop Omul (Etempvar _t'1 tdouble)
                            (Etempvar _t'2 tdouble) tdouble) tdouble)))))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tuint)
                    (Econst_int (Int.repr 1) tint) tuint))))
            (Sassign
              (Efield
                (Ederef (Etempvar _w (tptr (Tstruct _dotprod_task noattr)))
                  (Tstruct _dotprod_task noattr)) _result tdouble)
              (Etempvar _result tdouble))))))))
|}.

Definition f_dotprod := {|
  fn_return := tdouble;
  fn_callconv := cc_default;
  fn_params := ((_vec1, (tptr tdouble)) :: (_vec2, (tptr tdouble)) ::
                (_n, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_result, tdouble) :: (_T, tuint) :: (_t, tuint) ::
               (_delta, tuint) :: (_delta_next, tuint) ::
               (_delta_next__1, tuint) ::
               (_t'6, (tptr (Tstruct _dotprod_task noattr))) ::
               (_t'5, (tptr (Tstruct _dotprod_task noattr))) ::
               (_t'4, (tptr (Tstruct _dotprod_task noattr))) ::
               (_t'3, (tptr (Tstruct _task noattr))) :: (_t'2, tdouble) ::
               (_t'1, (tptr (Tstruct _dotprod_task noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _T (Evar _num_threads tuint))
  (Ssequence
    (Sset _delta (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Ssequence
        (Sset _t (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _t tuint) (Etempvar _T tuint)
                           tint)
              Sskip
              Sbreak)
            (Ssequence
              (Ssequence
                (Sset _t'6
                  (Evar _dtasks (tptr (Tstruct _dotprod_task noattr))))
                (Sassign
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Etempvar _t'6 (tptr (Tstruct _dotprod_task noattr)))
                        (Etempvar _t tuint)
                        (tptr (Tstruct _dotprod_task noattr)))
                      (Tstruct _dotprod_task noattr)) _vec1 (tptr tdouble))
                  (Ebinop Oadd (Etempvar _vec1 (tptr tdouble))
                    (Etempvar _delta tuint) (tptr tdouble))))
              (Ssequence
                (Ssequence
                  (Sset _t'5
                    (Evar _dtasks (tptr (Tstruct _dotprod_task noattr))))
                  (Sassign
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Etempvar _t'5 (tptr (Tstruct _dotprod_task noattr)))
                          (Etempvar _t tuint)
                          (tptr (Tstruct _dotprod_task noattr)))
                        (Tstruct _dotprod_task noattr)) _vec2 (tptr tdouble))
                    (Ebinop Oadd (Etempvar _vec2 (tptr tdouble))
                      (Etempvar _delta tuint) (tptr tdouble))))
                (Ssequence
                  (Sset _delta_next__1
                    (Ecast
                      (Ebinop Odiv
                        (Ebinop Omul
                          (Ecast
                            (Ebinop Oadd (Etempvar _t tuint)
                              (Econst_int (Int.repr 1) tint) tuint) tulong)
                          (Ecast (Etempvar _n tuint) tulong) tulong)
                        (Ecast (Etempvar _T tuint) tulong) tulong) tuint))
                  (Ssequence
                    (Ssequence
                      (Sset _t'4
                        (Evar _dtasks (tptr (Tstruct _dotprod_task noattr))))
                      (Sassign
                        (Efield
                          (Ederef
                            (Ebinop Oadd
                              (Etempvar _t'4 (tptr (Tstruct _dotprod_task noattr)))
                              (Etempvar _t tuint)
                              (tptr (Tstruct _dotprod_task noattr)))
                            (Tstruct _dotprod_task noattr)) _n tuint)
                        (Ebinop Osub (Etempvar _delta_next__1 tuint)
                          (Etempvar _delta tuint) tuint)))
                    (Sset _delta (Etempvar _delta_next__1 tuint)))))))
          (Sset _t
            (Ebinop Oadd (Etempvar _t tuint) (Econst_int (Int.repr 1) tint)
              tuint))))
      (Ssequence
        (Ssequence
          (Sset _t'3 (Evar _tasks (tptr (Tstruct _task noattr))))
          (Scall None
            (Evar _do_tasks (Tfunction
                              (Tcons (tptr (Tstruct _task noattr))
                                (Tcons tuint Tnil)) tvoid cc_default))
            ((Etempvar _t'3 (tptr (Tstruct _task noattr))) ::
             (Etempvar _T tuint) :: nil)))
        (Ssequence
          (Sset _result
            (Econst_float (Float.of_bits (Int64.repr 0)) tdouble))
          (Ssequence
            (Ssequence
              (Sset _t (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _t tuint)
                                 (Etempvar _T tuint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sset _t'1
                      (Evar _dtasks (tptr (Tstruct _dotprod_task noattr))))
                    (Ssequence
                      (Sset _t'2
                        (Efield
                          (Ederef
                            (Ebinop Oadd
                              (Etempvar _t'1 (tptr (Tstruct _dotprod_task noattr)))
                              (Etempvar _t tuint)
                              (tptr (Tstruct _dotprod_task noattr)))
                            (Tstruct _dotprod_task noattr)) _result tdouble))
                      (Sset _result
                        (Ebinop Oadd (Etempvar _result tdouble)
                          (Etempvar _t'2 tdouble) tdouble)))))
                (Sset _t
                  (Ebinop Oadd (Etempvar _t tuint)
                    (Econst_int (Int.repr 1) tint) tuint))))
            (Sreturn (Some (Etempvar _result tdouble)))))))))
|}.

Definition f_make_dotprod_tasks := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_T, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t, tuint) :: (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr (Tstruct _task noattr))) ::
               (_t'5, (tptr (Tstruct _dotprod_task noattr))) ::
               (_t'4, (tptr (Tstruct _dotprod_task noattr))) ::
               (_t'3, (tptr (Tstruct _task noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _make_tasks (Tfunction (Tcons tuint Tnil)
                          (tptr (Tstruct _task noattr)) cc_default))
      ((Etempvar _T tuint) :: nil))
    (Sassign (Evar _tasks (tptr (Tstruct _task noattr)))
      (Etempvar _t'1 (tptr (Tstruct _task noattr)))))
  (Ssequence
    (Sassign (Evar _num_threads tuint) (Etempvar _T tuint))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                          cc_default))
          ((Ebinop Omul (Etempvar _T tuint)
             (Esizeof (Tstruct _dotprod_task noattr) tuint) tuint) :: nil))
        (Sassign (Evar _dtasks (tptr (Tstruct _dotprod_task noattr)))
          (Ecast (Etempvar _t'2 (tptr tvoid))
            (tptr (Tstruct _dotprod_task noattr)))))
      (Ssequence
        (Ssequence
          (Sset _t'5 (Evar _dtasks (tptr (Tstruct _dotprod_task noattr))))
          (Sifthenelse (Eunop Onotbool
                         (Etempvar _t'5 (tptr (Tstruct _dotprod_task noattr)))
                         tint)
            (Scall None
              (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
              ((Econst_int (Int.repr 1) tint) :: nil))
            Sskip))
        (Ssequence
          (Sset _t (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _t tuint)
                             (Etempvar _T tuint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sset _t'3 (Evar _tasks (tptr (Tstruct _task noattr))))
                (Ssequence
                  (Sset _t'4
                    (Evar _dtasks (tptr (Tstruct _dotprod_task noattr))))
                  (Scall None
                    (Evar _initialize_task (Tfunction
                                             (Tcons
                                               (tptr (Tstruct _task noattr))
                                               (Tcons tuint
                                                 (Tcons
                                                   (tptr (Tfunction
                                                           (Tcons
                                                             (tptr tvoid)
                                                             Tnil) tvoid
                                                           cc_default))
                                                   (Tcons (tptr tvoid) Tnil))))
                                             tvoid cc_default))
                    ((Etempvar _t'3 (tptr (Tstruct _task noattr))) ::
                     (Etempvar _t tuint) ::
                     (Evar _dotprod_worker (Tfunction
                                             (Tcons (tptr tvoid) Tnil) tvoid
                                             cc_default)) ::
                     (Ebinop Oadd
                       (Etempvar _t'4 (tptr (Tstruct _dotprod_task noattr)))
                       (Etempvar _t tuint)
                       (tptr (Tstruct _dotprod_task noattr))) :: nil)))))
            (Sset _t
              (Ebinop Oadd (Etempvar _t tuint) (Econst_int (Int.repr 1) tint)
                tuint))))))))
|}.

Definition composites : list composite_definition :=
(Composite _dotprod_task Struct
   (Member_plain _vec1 (tptr tdouble) :: Member_plain _vec2 (tptr tdouble) ::
    Member_plain _n tuint :: Member_plain _result tdouble :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Tsingle :: nil) AST.Tsingle cc_default))
     (Tcons tfloat Tnil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons tint (Tcons tint Tnil)) tint
     cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_make_tasks,
   Gfun(External (EF_external "make_tasks"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) (tptr (Tstruct _task noattr)) cc_default)) ::
 (_initialize_task,
   Gfun(External (EF_external "initialize_task"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _task noattr))
       (Tcons tuint
         (Tcons (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
           (Tcons (tptr tvoid) Tnil)))) tvoid cc_default)) ::
 (_do_tasks,
   Gfun(External (EF_external "do_tasks"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr (Tstruct _task noattr)) (Tcons tuint Tnil)) tvoid
     cc_default)) :: (_tasks, Gvar v_tasks) ::
 (_num_threads, Gvar v_num_threads) :: (_dtasks, Gvar v_dtasks) ::
 (_dotprod_worker, Gfun(Internal f_dotprod_worker)) ::
 (_dotprod, Gfun(Internal f_dotprod)) ::
 (_make_dotprod_tasks, Gfun(Internal f_make_dotprod_tasks)) :: nil).

Definition public_idents : list ident :=
(_make_dotprod_tasks :: _dotprod :: _dotprod_worker :: _dtasks ::
 _num_threads :: _tasks :: _do_tasks :: _initialize_task :: _make_tasks ::
 _malloc :: _exit :: ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_expect :: ___builtin_unreachable ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


