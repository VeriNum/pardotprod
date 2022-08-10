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
  Definition source_file := "parsplit.c".
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
Definition _arg : ident := $"arg".
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
Definition _done : ident := $"done".
Definition _dotprod : ident := $"dotprod".
Definition _dotprod_task : ident := $"dotprod_task".
Definition _dotprod_worker : ident := $"dotprod_worker".
Definition _dtasks : ident := $"dtasks".
Definition _exit : ident := $"exit".
Definition _f : ident := $"f".
Definition _fprintf : ident := $"fprintf".
Definition _freelock : ident := $"freelock".
Definition _go : ident := $"go".
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
Definition _thread_worker : ident := $"thread_worker".
Definition _vec1 : ident := $"vec1".
Definition _vec2 : ident := $"vec2".
Definition _w : ident := $"w".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.

Definition f_thread_worker := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_arg, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t, (tptr (Tstruct _task noattr))) ::
               (_t'4, (tptr (Tstruct _atom_int noattr))) ::
               (_t'3, (tptr tvoid)) ::
               (_t'2,
                (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))) ::
               (_t'1, (tptr (Tstruct _atom_int noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t
    (Ecast (Etempvar _arg (tptr tvoid)) (tptr (Tstruct _task noattr))))
  (Sloop
    (Ssequence
      Sskip
      (Ssequence
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef (Etempvar _t (tptr (Tstruct _task noattr)))
                (Tstruct _task noattr)) _go
              (tptr (Tstruct _atom_int noattr))))
          (Scall None
            (Evar _acquire (Tfunction
                             (Tcons (tptr (Tstruct _atom_int noattr)) Tnil)
                             tvoid cc_default))
            ((Etempvar _t'4 (tptr (Tstruct _atom_int noattr))) :: nil)))
        (Ssequence
          (Ssequence
            (Sset _t'2
              (Efield
                (Ederef (Etempvar _t (tptr (Tstruct _task noattr)))
                  (Tstruct _task noattr)) _f
                (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))))
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef (Etempvar _t (tptr (Tstruct _task noattr)))
                    (Tstruct _task noattr)) _closure (tptr tvoid)))
              (Scall None
                (Etempvar _t'2 (tptr (Tfunction (Tcons (tptr tvoid) Tnil)
                                       tvoid cc_default)))
                ((Etempvar _t'3 (tptr tvoid)) :: nil))))
          (Ssequence
            (Sset _t'1
              (Efield
                (Ederef (Etempvar _t (tptr (Tstruct _task noattr)))
                  (Tstruct _task noattr)) _done
                (tptr (Tstruct _atom_int noattr))))
            (Scall None
              (Evar _release (Tfunction
                               (Tcons (tptr (Tstruct _atom_int noattr)) Tnil)
                               tvoid cc_default))
              ((Etempvar _t'1 (tptr (Tstruct _atom_int noattr))) :: nil))))))
    Sskip))
|}.

Definition f_make_tasks := {|
  fn_return := (tptr (Tstruct _task noattr));
  fn_callconv := cc_default;
  fn_params := ((_T, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_tasks, (tptr (Tstruct _task noattr))) :: (_i, tuint) ::
               (_t, (tptr (Tstruct _task noattr))) ::
               (_t'3, (tptr (Tstruct _atom_int noattr))) ::
               (_t'2, (tptr (Tstruct _atom_int noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Ebinop Omul (Etempvar _T tuint)
         (Esizeof (Tstruct _task noattr) tuint) tuint) :: nil))
    (Sset _tasks
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _task noattr)))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool
                   (Etempvar _tasks (tptr (Tstruct _task noattr))) tint)
      (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 1) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tuint) (Etempvar _T tuint)
                           tint)
              Sskip
              Sbreak)
            (Ssequence
              (Sset _t
                (Ebinop Oadd (Etempvar _tasks (tptr (Tstruct _task noattr)))
                  (Etempvar _i tuint) (tptr (Tstruct _task noattr))))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'2)
                    (Evar _makelock (Tfunction Tnil
                                      (tptr (Tstruct _atom_int noattr))
                                      cc_default)) nil)
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _t (tptr (Tstruct _task noattr)))
                        (Tstruct _task noattr)) _go
                      (tptr (Tstruct _atom_int noattr)))
                    (Etempvar _t'2 (tptr (Tstruct _atom_int noattr)))))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'3)
                      (Evar _makelock (Tfunction Tnil
                                        (tptr (Tstruct _atom_int noattr))
                                        cc_default)) nil)
                    (Sassign
                      (Efield
                        (Ederef (Etempvar _t (tptr (Tstruct _task noattr)))
                          (Tstruct _task noattr)) _done
                        (tptr (Tstruct _atom_int noattr)))
                      (Etempvar _t'3 (tptr (Tstruct _atom_int noattr)))))
                  (Scall None
                    (Evar _spawn (Tfunction
                                   (Tcons
                                     (tptr (Tfunction
                                             (Tcons (tptr tvoid) Tnil) tint
                                             cc_default))
                                     (Tcons (tptr tvoid) Tnil)) tvoid
                                   cc_default))
                    ((Evar _thread_worker (Tfunction
                                            (Tcons (tptr tvoid) Tnil) tint
                                            cc_default)) ::
                     (Etempvar _t (tptr (Tstruct _task noattr))) :: nil))))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
              tuint))))
      (Sreturn (Some (Etempvar _tasks (tptr (Tstruct _task noattr))))))))
|}.

Definition f_initialize_task := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_tasks, (tptr (Tstruct _task noattr))) :: (_i, tuint) ::
                (_f,
                 (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))) ::
                (_closure, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef
        (Ebinop Oadd (Etempvar _tasks (tptr (Tstruct _task noattr)))
          (Etempvar _i tuint) (tptr (Tstruct _task noattr)))
        (Tstruct _task noattr)) _f
      (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default)))
    (Etempvar _f (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))))
  (Sassign
    (Efield
      (Ederef
        (Ebinop Oadd (Etempvar _tasks (tptr (Tstruct _task noattr)))
          (Etempvar _i tuint) (tptr (Tstruct _task noattr)))
        (Tstruct _task noattr)) _closure (tptr tvoid))
    (Etempvar _closure (tptr tvoid))))
|}.

Definition f_do_tasks := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_tasks, (tptr (Tstruct _task noattr))) :: (_T, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_t'4, (tptr (Tstruct _atom_int noattr))) ::
               (_t'3, (tptr tvoid)) ::
               (_t'2,
                (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))) ::
               (_t'1, (tptr (Tstruct _atom_int noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 1) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint) (Etempvar _T tuint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef
                (Ebinop Oadd (Etempvar _tasks (tptr (Tstruct _task noattr)))
                  (Etempvar _i tint) (tptr (Tstruct _task noattr)))
                (Tstruct _task noattr)) _go
              (tptr (Tstruct _atom_int noattr))))
          (Scall None
            (Evar _release (Tfunction
                             (Tcons (tptr (Tstruct _atom_int noattr)) Tnil)
                             tvoid cc_default))
            ((Etempvar _t'4 (tptr (Tstruct _atom_int noattr))) :: nil))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef
            (Ebinop Oadd (Etempvar _tasks (tptr (Tstruct _task noattr)))
              (Econst_int (Int.repr 0) tint) (tptr (Tstruct _task noattr)))
            (Tstruct _task noattr)) _f
          (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))))
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef
              (Ebinop Oadd (Etempvar _tasks (tptr (Tstruct _task noattr)))
                (Econst_int (Int.repr 0) tint) (tptr (Tstruct _task noattr)))
              (Tstruct _task noattr)) _closure (tptr tvoid)))
        (Scall None
          (Etempvar _t'2 (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                 cc_default)))
          ((Etempvar _t'3 (tptr tvoid)) :: nil))))
    (Ssequence
      (Sset _i (Econst_int (Int.repr 1) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tint) (Etempvar _T tuint)
                         tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _t'1
              (Efield
                (Ederef
                  (Ebinop Oadd
                    (Etempvar _tasks (tptr (Tstruct _task noattr)))
                    (Etempvar _i tint) (tptr (Tstruct _task noattr)))
                  (Tstruct _task noattr)) _done
                (tptr (Tstruct _atom_int noattr))))
            (Scall None
              (Evar _acquire (Tfunction
                               (Tcons (tptr (Tstruct _atom_int noattr)) Tnil)
                               tvoid cc_default))
              ((Etempvar _t'1 (tptr (Tstruct _atom_int noattr))) :: nil))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))))
|}.

Definition composites : list composite_definition :=
(Composite _task Struct
   (Member_plain _go (tptr (Tstruct _atom_int noattr)) ::
    Member_plain _done (tptr (Tstruct _atom_int noattr)) ::
    Member_plain _f
      (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
    Member_plain _closure (tptr tvoid) :: nil)
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
 (_makelock,
   Gfun(External (EF_external "makelock"
                   (mksignature nil AST.Tint cc_default)) Tnil
     (tptr (Tstruct _atom_int noattr)) cc_default)) ::
 (_acquire,
   Gfun(External (EF_external "acquire"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _atom_int noattr)) Tnil) tvoid cc_default)) ::
 (_release,
   Gfun(External (EF_external "release"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _atom_int noattr)) Tnil) tvoid cc_default)) ::
 (_spawn,
   Gfun(External (EF_external "spawn"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tint cc_default))
       (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (_thread_worker, Gfun(Internal f_thread_worker)) ::
 (_make_tasks, Gfun(Internal f_make_tasks)) ::
 (_initialize_task, Gfun(Internal f_initialize_task)) ::
 (_do_tasks, Gfun(Internal f_do_tasks)) :: nil).

Definition public_idents : list ident :=
(_do_tasks :: _initialize_task :: _make_tasks :: _thread_worker :: _spawn ::
 _release :: _acquire :: _makelock :: _malloc :: _exit :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_expect :: ___builtin_unreachable :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


