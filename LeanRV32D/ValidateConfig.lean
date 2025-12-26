import LeanRV32D.Option
import LeanRV32D.Flow
import LeanRV32D.Prelude
import LeanRV32D.Xlen
import LeanRV32D.Vlen
import LeanRV32D.PlatformConfig
import LeanRV32D.Extensions
import LeanRV32D.PmpRegs
import LeanRV32D.Pma

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open ConcurrencyInterfaceV1

noncomputable section

namespace LeanRV32D.Functions

open zvk_vsm4r_funct6
open zvk_vsha2_funct6
open zvk_vaesem_funct6
open zvk_vaesef_funct6
open zvk_vaesdm_funct6
open zvk_vaesdf_funct6
open zicondop
open xRET_type
open wxfunct6
open wvxfunct6
open wvvfunct6
open wvfunct6
open wrsop
open write_kind
open wmvxfunct6
open wmvvfunct6
open vxsgfunct6
open vxmsfunct6
open vxmfunct6
open vxmcfunct6
open vxfunct6
open vxcmpfunct6
open vvmsfunct6
open vvmfunct6
open vvmcfunct6
open vvfunct6
open vvcmpfunct6
open vregno
open vregidx
open vmlsop
open vlewidth
open visgfunct6
open virtaddr
open vimsfunct6
open vimfunct6
open vimcfunct6
open vifunct6
open vicmpfunct6
open vfwunary0
open vfunary1
open vfunary0
open vfnunary0
open vextfunct6
open vector_support
open uop
open sopw
open sop
open seed_opst
open rounding_mode
open ropw
open rop
open rmvvfunct6
open rivvfunct6
open rfwvvfunct6
open rfvvfunct6
open regno
open regidx
open read_kind
open pte_check_failure
open pmpAddrMatch
open physaddr
open option
open nxsfunct6
open nxfunct6
open nvsfunct6
open nvfunct6
open ntl_type
open nisfunct6
open nifunct6
open mvxmafunct6
open mvxfunct6
open mvvmafunct6
open mvvfunct6
open mmfunct6
open misaligned_fault
open maskfunct3
open landing_pad_expectation
open iop
open instruction
open indexed_mop
open fwvvmafunct6
open fwvvfunct6
open fwvfunct6
open fwvfmafunct6
open fwvffunct6
open fwffunct6
open fvvmfunct6
open fvvmafunct6
open fvvfunct6
open fvfmfunct6
open fvfmafunct6
open fvffunct6
open fregno
open fregidx
open float_class
open f_un_x_op_H
open f_un_x_op_D
open f_un_rm_xf_op_S
open f_un_rm_xf_op_H
open f_un_rm_xf_op_D
open f_un_rm_fx_op_S
open f_un_rm_fx_op_H
open f_un_rm_fx_op_D
open f_un_rm_ff_op_S
open f_un_rm_ff_op_H
open f_un_rm_ff_op_D
open f_un_op_x_S
open f_un_op_f_S
open f_un_f_op_H
open f_un_f_op_D
open f_madd_op_S
open f_madd_op_H
open f_madd_op_D
open f_bin_x_op_H
open f_bin_x_op_D
open f_bin_rm_op_S
open f_bin_rm_op_H
open f_bin_rm_op_D
open f_bin_op_x_S
open f_bin_op_f_S
open f_bin_f_op_H
open f_bin_f_op_D
open extop_zbb
open extension
open exception
open ctl_result
open csrop
open cregidx
open checked_cbop
open cfregidx
open cbop_zicbop
open cbop_zicbom
open cbie
open bropw_zbb
open brop_zbs
open brop_zbkb
open brop_zbb
open breakpoint_cause
open bop
open biop_zbs
open barrier_kind
open amoop
open agtype
open WaitReason
open VectorHalf
open TrapVectorMode
open TrapCause
open Step
open Software_Check_Code
open Signedness
open SWCheckCodes
open SATPMode
open Reservability
open Register
open Privilege
open PmpAddrMatchType
open PTW_Error
open PTE_Check
open MemoryAccessType
open InterruptType
open ISA_Format
open HartState
open FetchResult
open Ext_DataAddr_Check
open ExtStatus
open ExecutionResult
open ExceptionType
open CSRAccessType
open AtomicSupport
open Architecture

def check_privs (_ : Unit) : Bool :=
  if (((hartSupports Ext_S) && (not (hartSupports Ext_U))) : Bool)
  then
    (let _ : Unit :=
      (print_endline "User mode (U) should be enabled if supervisor mode (S) is enabled.")
    false)
  else true

def check_mmu_config (_ : Unit) : SailM Bool := do
  let valid : Bool := true
  assert (xlen == 32) "postlude/validate_config.sail:43.21-43.22"
  let _ : Unit :=
    if (((not (hartSupports Ext_S)) && (hartSupports Ext_Sv32)) : Bool)
    then
      (let valid : Bool := false
      (print_endline
        "Supervisor mode (S) is disabled but Sv32 is enabled: cannot support address translation without supervisor mode."))
    else ()
  if (((hartSupports Ext_Sv39) || ((hartSupports Ext_Sv48) || (hartSupports Ext_Sv57))) : Bool)
  then
    (let valid : Bool := false
    (pure (print_endline
        "One or more of Sv39/Sv48/Sv57 is enabled: these are not supported on RV32.")))
  else (pure ())
  if (((hartSupports Ext_Svrsw60t59b) && (not (hartSupports Ext_Sv39))) : Bool)
  then
    (let valid : Bool := false
    let _ : Unit :=
      (print_endline
        "Svrsw60t59b is enabled but Sv39 is disabled: supporting Svrsw60t59b requires supporting Sv39.")
    (pure valid))
  else (pure valid)

def check_vlen_elen (_ : Unit) : Bool :=
  if (((vlen_exp : Nat) <b (elen_exp : Nat)) : Bool)
  then
    (let _ : Unit :=
      (print_endline
        (HAppend.hAppend "VLEN (set to 2^"
          (HAppend.hAppend (Int.repr vlen_exp)
            (HAppend.hAppend ") cannot be less than ELEN (set to 2^"
              (HAppend.hAppend (Int.repr elen_exp) ").")))))
    false)
  else
    (if ((((vlen_exp : Nat) <b 3) || (((vlen_exp : Nat) >b 16) : Bool)) : Bool)
    then
      (let _ : Unit :=
        (print_endline
          (HAppend.hAppend "VLEN set to 2^"
            (HAppend.hAppend (Int.repr vlen_exp) " but must be within [2^3, 2^16].")))
      false)
    else
      (if ((((elen_exp : Nat) <b 3) || (((elen_exp : Nat) >b 16) : Bool)) : Bool)
      then
        (let _ : Unit :=
          (print_endline
            (HAppend.hAppend "ELEN set to 2^"
              (HAppend.hAppend (Int.repr elen_exp) " but must be within [2^3, 2^16].")))
        false)
      else true))

def check_vext_config (_ : Unit) : Bool :=
  let valid : Bool := true
  let valid : Bool :=
    if (((vector_support_ge vector_support_level Integer) && (((elen_exp : Nat) <b 5) : Bool)) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          (HAppend.hAppend "Zve*x is enabled but ELEN is 2^"
            (HAppend.hAppend (Int.repr elen_exp) ": ELEN must be >= 2^5")))
      valid)
    else valid
  let valid : Bool :=
    if (((vector_support_ge vector_support_level Float_single) && (not (hartSupports Ext_F))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline "Zve*f is enabled but F is disabled: supporting Zve*f requires F.")
      valid)
    else valid
  let valid : Bool :=
    if ((vector_support_ge vector_support_level Float_double) : Bool)
    then
      (let valid : Bool :=
        if (((elen_exp : Nat) <b 6) : Bool)
        then
          (let valid : Bool := false
          let _ : Unit :=
            (print_endline
              (HAppend.hAppend "Zve*d is enabled but ELEN is 2^"
                (HAppend.hAppend (Int.repr elen_exp) ": ELEN must be >= 2^6")))
          valid)
        else valid
      if ((not (hartSupports Ext_D)) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline "Zve*d is enabled but D is disabled: supporting Zve*d requires D.")
        valid)
      else valid)
    else valid
  let valid : Bool :=
    if (((hartSupports Ext_Zve32x) && (not (hartSupports Ext_Zicsr))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline "Zve32x is enabled but Zicsr is disabled: supporting Zve32x requires Zicsr.")
      valid)
    else valid
  let valid : Bool :=
    if (((hartSupports Ext_Zve32x) && (not (hartSupports Ext_Zvl32b))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          (HAppend.hAppend "VLEN (set to 2^"
            (HAppend.hAppend (Int.repr vlen_exp)
              ") is below the minimum required for Zve32x (need Zvl32b).")))
      valid)
    else valid
  let valid : Bool :=
    if (((hartSupports Ext_Zve64x) && (not (hartSupports Ext_Zvl64b))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          (HAppend.hAppend "VLEN (set to 2^"
            (HAppend.hAppend (Int.repr vlen_exp)
              ") is below the minimum required for Zve64x (need Zvl64b).")))
      valid)
    else valid
  let valid : Bool :=
    if (((vector_support_ge vector_support_level Full) && (not (hartSupports Ext_Zvl128b))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          (HAppend.hAppend "VLEN (set to 2^"
            (HAppend.hAppend (Int.repr vlen_exp)
              ") is below the minimum required for V (need Zvl128b).")))
      valid)
    else valid
  let valid : Bool :=
    if (((hartSupports Ext_Zvfhmin) && (not (hartSupports Ext_Zve32f))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline "Zvfhmin is enabled but Zve32f is disabled: Zvfhmin requires Zve32f.")
      valid)
    else valid
  let valid : Bool :=
    if (((hartSupports Ext_Zvfh) && ((not (hartSupports Ext_Zve32f)) || (not
             (hartSupports Ext_Zfhmin)))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "Zvfh is enabled but Zve32f and/or Zfhmin are disabled: Zvfh requires Zve32f and Zfhmin.")
      valid)
    else valid
  let valid : Bool :=
    if (((hartSupports Ext_Zvbb) && (not (hartSupports Ext_Zve32x))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline "Zvbb is enabled but Zve32x is disabled: Zvbb requires Zve32x.")
      valid)
    else valid
  let valid : Bool :=
    if (((hartSupports Ext_Zvbc) && (not ((hartSupports Ext_Zve64x) || (hartSupports Ext_V)))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline "Zvbc is enabled but Zve64x and V are disabled: Zvbc requires Zve64x or V.")
      valid)
    else valid
  let valid : Bool :=
    if (((hartSupports Ext_Zvkb) && (not (hartSupports Ext_Zve32x))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline "Zvkb is enabled but Zve32x is disabled: Zvkb requires Zve32x.")
      valid)
    else valid
  let valid : Bool :=
    if (((hartSupports Ext_Zvkg) && (not (hartSupports Ext_Zve32x))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline "Zvkg is enabled but Zve32x is disabled: Zvkg requires Zve32x.")
      valid)
    else valid
  let valid : Bool :=
    if (((hartSupports Ext_Zvkned) && (not (hartSupports Ext_Zve32x))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline "Zvkned is enabled but Zve32x is disabled: Zvkned requires Zve32x.")
      valid)
    else valid
  let valid : Bool :=
    if (((hartSupports Ext_Zvknha) && (not (hartSupports Ext_Zve32x))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline "Zvknha is enabled but Zve32x is disabled: Zvknha requires Zve32x.")
      valid)
    else valid
  let valid : Bool :=
    if (((hartSupports Ext_Zvknhb) && (not ((hartSupports Ext_Zve64x) || (hartSupports Ext_V)))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "Zvknhb is enabled but Zve64x and V are disabled: Zvknhb requires Zve64x or V.")
      valid)
    else valid
  let valid : Bool :=
    if (((hartSupports Ext_Zvksed) && (not (hartSupports Ext_Zve32x))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline "Zvksed is enabled but Zve32x is disabled: Zvksed requires Zve32x.")
      valid)
    else valid
  let valid : Bool :=
    if (((hartSupports Ext_Zvksh) && (not (hartSupports Ext_Zve32x))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline "Zvksh is enabled but Zve32x is disabled: Zvksh requires Zve32x.")
      valid)
    else valid
  if (((hartSupports Ext_Zvkt) && (not (hartSupports Ext_Zve32x))) : Bool)
  then
    (let valid : Bool := false
    let _ : Unit := (print_endline "Zvkt is enabled but Zve32x is disabled: Zvkt requires Zve32x.")
    valid)
  else valid

def check_pma_regions (pmas : (List PMA_Region)) (prev_base : (BitVec 64)) (prev_size : (BitVec 64)) : Bool :=
  match pmas with
  | [] => true
  | (pma :: rest) =>
    (if ((zopz0zI_u pma.base (prev_base + prev_size)) : Bool)
    then
      (let _ : Unit :=
        (print_endline
          (HAppend.hAppend "Memory region starting at "
            (HAppend.hAppend (BitVec.toFormatted pma.base)
              (HAppend.hAppend " is not above the end of the previous region starting at "
                (HAppend.hAppend (BitVec.toFormatted prev_base)
                  (HAppend.hAppend " and ending at "
                    (HAppend.hAppend (BitVec.toFormatted (prev_base + prev_size)) ".")))))))
      false)
    else (check_pma_regions rest pma.base pma.size))

def dtb_within_configured_pma_memory (addr : (BitVec 64)) (size : (BitVec 64)) : SailM Bool := do
  (pure (is_some (matching_pma_bits_range (← readReg pma_regions) addr size)))

def check_mem_layout (_ : Unit) : SailM Bool := do
  if (((← readReg pma_regions) == []) : Bool)
  then
    (let _ : Unit := (print_endline "No memory regions specified.")
    (pure false))
  else (pure (check_pma_regions (← readReg pma_regions) (zeros (n := 64)) (zeros (n := 64))))

def check_pmp (_ : Unit) : Bool :=
  let valid : Bool := true
  let valid : Bool :=
    if (((true : Bool) && (sys_pmp_grain != 0)) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit := (print_endline "NA4 is not supported if the PMP grain G is non-zero.")
      valid)
    else valid
  if ((sys_pmp_usable_count >b sys_pmp_count) : Bool)
  then
    (let valid : Bool := false
    let _ : Unit :=
      (print_endline
        "The number of usable PMP entries cannot exceed the total number of PMP entries.")
    valid)
  else valid

/-- Type quantifiers: k_ex691144_ : Bool -/
def check_required_sstvala_option (name : String) (value : Bool) : Bool :=
  if ((not value) : Bool)
  then
    (let _ : Unit :=
      (print_endline
        (HAppend.hAppend "The Sstvala extension is enabled but "
          (HAppend.hAppend name
            " have not been configured (under `base.xtval_nonzero`) to write xtval.")))
    false)
  else true

def check_misc_extension_dependencies (_ : Unit) : Bool :=
  let valid : Bool := true
  let valid : Bool :=
    if (((hartSupports Ext_F) && (hartSupports Ext_Zfinx)) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "The F and Zfinx extensions are mutually exclusive and cannot be supported simultaneously.")
      valid)
    else valid
  let valid : Bool :=
    if (((hartSupports Ext_Zfinx) && (not (hartSupports Ext_Zicsr))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "The Zfinx extensions is enabled but Zicsr is disabled: supporting Zfinx requires Zicsr.")
      valid)
    else valid
  let valid : Bool :=
    if (((hartSupports Ext_Zdinx) && (not (hartSupports Ext_Zfinx))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "The Zdinx extensions is enabled but Zfinx is disabled: supporting Zdinx requires Zfinx.")
      valid)
    else valid
  let valid : Bool :=
    if (((hartSupports Ext_Zhinx) && (not (hartSupports Ext_Zfinx))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "The Zhinx extensions is enabled but Zfinx is disabled: supporting Zhinx requires Zfinx.")
      valid)
    else valid
  let valid : Bool :=
    if (((hartSupports Ext_Zhinxmin) && (not (hartSupports Ext_Zfinx))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "The Zhinxmin extensions is enabled but Zfinx is disabled: supporting Zhinxmin requires Zfinx.")
      valid)
    else valid
  let valid : Bool :=
    if (((hartSupports Ext_Zicfilp) && (not (hartSupports Ext_Zicsr))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "The Zicfilp extension is enabled but Zicsr is disabled: supporting Zicfilp requires Zicsr.")
      valid)
    else valid
  let valid : Bool :=
    if (((hartSupports Ext_Zfbfmin) && (not (hartSupports Ext_F))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "The Zfbfmin extension is enabled but F is disabled: supporting Zfbfmin requires F.")
      valid)
    else valid
  let valid : Bool :=
    if (((hartSupports Ext_Zvfbfmin) && (not (hartSupports Ext_Zve32f))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "The Zvfbfmin extension is enabled but Zve32f is disabled: supporting Zvfbfmin requires Zve32f.")
      valid)
    else valid
  let valid : Bool :=
    if (((hartSupports Ext_Zvfbfwma) && ((not (hartSupports Ext_Zfbfmin)) || (not
             (hartSupports Ext_Zvfbfmin)))) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline
          "The Zvfbfwma extension is enabled but either Zfbfmin or Zvfbfmin is disabled: supporting Zvfbfwma requires Zfbfmin and Zvfbfmin.")
      valid)
    else valid
  if ((hartSupports Ext_Sstvala) : Bool)
  then
    (let valid : Bool :=
      if ((not (hartSupports Ext_S)) : Bool)
      then
        (let valid : Bool := false
        let _ : Unit :=
          (print_endline
            "The Sstvala extension writes `stval` which requires supervisor mode (S) but supervisor mode is not enabled.")
        valid)
      else valid
    let valid : Bool :=
      (valid && (check_required_sstvala_option "load page-faults" load_page_fault_writes_xtval))
    let valid : Bool :=
      (valid && (check_required_sstvala_option "load access-faults" load_access_fault_writes_xtval))
    let valid : Bool :=
      (valid && (check_required_sstvala_option "misaligned load exceptions"
          misaligned_load_writes_xtval))
    let valid : Bool :=
      (valid && (check_required_sstvala_option "store/AMO page-faults" samo_page_fault_writes_xtval))
    let valid : Bool :=
      (valid && (check_required_sstvala_option "store/AMO access-faults"
          samo_access_fault_writes_xtval))
    let valid : Bool :=
      (valid && (check_required_sstvala_option "misaligned store/AMO exceptions"
          misaligned_samo_writes_xtval))
    let valid : Bool :=
      (valid && (check_required_sstvala_option "fetch page-faults" fetch_page_fault_writes_xtval))
    let valid : Bool :=
      (valid && (check_required_sstvala_option "fetch access-faults" fetch_access_fault_writes_xtval))
    let valid : Bool :=
      (valid && (check_required_sstvala_option "misaligned fetch exceptions"
          misaligned_fetch_writes_xtval))
    let valid : Bool :=
      (valid && (check_required_sstvala_option "hardware breakpoint exceptions"
          hardware_breakpoint_writes_xtval))
    (valid && (check_required_sstvala_option "illegal instruction exceptions"
        illegal_instruction_writes_xtval)))
  else valid

def check_extension_param_constraints (_ : Unit) : Bool :=
  let valid : Bool := true
  let valid : Bool :=
    if (((hartSupports Ext_Zic64b) && (plat_cache_block_size_exp != 6)) : Bool)
    then
      (let valid : Bool := false
      let _ : Unit :=
        (print_endline "The Zic64b extension is enabled but the cache block size is not 64 bytes.")
      valid)
    else valid
  let min_rss_exp := (log2_xlen -i 3)
  if ((((hartSupports Ext_A) || (hartSupports Ext_Zalrsc)) && (plat_reservation_set_size_exp <b min_rss_exp)) : Bool)
  then
    (let valid : Bool := false
    let _ : Unit :=
      (print_endline
        (HAppend.hAppend
          "The A or Zalrsc extensions are enabled, but the reservation set size of 2^"
          (HAppend.hAppend (Int.repr plat_reservation_set_size_exp)
            (HAppend.hAppend " is too small; it should be at least 2^"
              (HAppend.hAppend (Int.repr min_rss_exp) " for the LR/SC operands on this platform.")))))
    valid)
  else valid

def config_is_valid (_ : Unit) : SailM Bool := do
  (pure ((check_privs ()) && ((← (check_mmu_config ())) && ((← (check_mem_layout ())) && ((check_vlen_elen
              ()) && ((check_vext_config ()) && ((check_pmp ()) && ((check_misc_extension_dependencies
                    ()) && (check_extension_param_constraints ())))))))))

