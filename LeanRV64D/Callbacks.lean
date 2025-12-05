import LeanRV64D.HexBits
import LeanRV64D.Xlen
import LeanRV64D.Types

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

noncomputable section

namespace LeanRV64D.Functions

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

/-- Type quantifiers: k_n : Nat, k_n ≥ 0, k_n ∈ {16, 32} -/
def fetch_callback (x_0 : (BitVec k_n)) : Unit :=
  ()

/-- Type quantifiers: x_2 : Nat, x_2 ≥ 0, 0 < x_2 ∧ x_2 ≤ max_mem_access -/
def mem_write_callback (x_0 : String) (x_1 : (BitVec (if ( 64 = 32  : Bool) then 34 else 64))) (x_2 : Nat) (x_3 : (BitVec (8 * x_2))) : Unit :=
  ()

/-- Type quantifiers: x_2 : Nat, x_2 ≥ 0, 0 < x_2 ∧ x_2 ≤ max_mem_access -/
def mem_read_callback (x_0 : String) (x_1 : (BitVec (if ( 64 = 32  : Bool) then 34 else 64))) (x_2 : Nat) (x_3 : (BitVec (8 * x_2))) : Unit :=
  ()

def mem_exception_callback (x_0 : (BitVec (if ( 64 = 32  : Bool) then 34 else 64))) (x_1 : (BitVec 6)) : Unit :=
  ()

def pc_write_callback (x_0 : (BitVec 64)) : Unit :=
  ()

def xreg_full_write_callback (x_0 : String) (x_1 : regidx) (x_2 : (BitVec 64)) : Unit :=
  ()

def csr_full_write_callback (x_0 : String) (x_1 : (BitVec 12)) (x_2 : (BitVec 64)) : Unit :=
  ()

def csr_full_read_callback (x_0 : String) (x_1 : (BitVec 12)) (x_2 : (BitVec 64)) : Unit :=
  ()

def redirect_callback (x_0 : (BitVec 64)) : Unit :=
  ()

/-- Type quantifiers: k_ex650112_ : Bool -/
def trap_callback (x_0 : Bool) (x_1 : (BitVec 6)) : Unit :=
  ()

def csr_name_map_backwards (arg_ : String) : SailM (BitVec 12) := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | "misa" => (some 0x301#12)
  | "mstatus" => (some 0x300#12)
  | "mstatush" => (some 0x310#12)
  | "mseccfg" => (some 0x747#12)
  | "mseccfgh" => (some 0x757#12)
  | "menvcfg" => (some 0x30A#12)
  | "menvcfgh" => (some 0x31A#12)
  | "senvcfg" => (some 0x10A#12)
  | "mie" => (some 0x304#12)
  | "mip" => (some 0x344#12)
  | "medeleg" => (some 0x302#12)
  | "medelegh" => (some 0x312#12)
  | "mideleg" => (some 0x303#12)
  | "mcause" => (some 0x342#12)
  | "mtval" => (some 0x343#12)
  | "mscratch" => (some 0x340#12)
  | "scounteren" => (some 0x106#12)
  | "mcounteren" => (some 0x306#12)
  | "mcountinhibit" => (some 0x320#12)
  | "mvendorid" => (some 0xF11#12)
  | "marchid" => (some 0xF12#12)
  | "mimpid" => (some 0xF13#12)
  | "mhartid" => (some 0xF14#12)
  | "mconfigptr" => (some 0xF15#12)
  | "sstatus" => (some 0x100#12)
  | "sip" => (some 0x144#12)
  | "sie" => (some 0x104#12)
  | "sscratch" => (some 0x140#12)
  | "scause" => (some 0x142#12)
  | "stval" => (some 0x143#12)
  | "tselect" => (some 0x7A0#12)
  | "tdata1" => (some 0x7A1#12)
  | "tdata2" => (some 0x7A2#12)
  | "tdata3" => (some 0x7A3#12)
  | "stvec" => (some 0x105#12)
  | "sepc" => (some 0x141#12)
  | "mtvec" => (some 0x305#12)
  | "mepc" => (some 0x341#12)
  | "pmpcfg0" => (some 0x3A0#12)
  | "pmpcfg1" => (some 0x3A1#12)
  | "pmpcfg2" => (some 0x3A2#12)
  | "pmpcfg3" => (some 0x3A3#12)
  | "pmpcfg4" => (some 0x3A4#12)
  | "pmpcfg5" => (some 0x3A5#12)
  | "pmpcfg6" => (some 0x3A6#12)
  | "pmpcfg7" => (some 0x3A7#12)
  | "pmpcfg8" => (some 0x3A8#12)
  | "pmpcfg9" => (some 0x3A9#12)
  | "pmpcfg10" => (some 0x3AA#12)
  | "pmpcfg11" => (some 0x3AB#12)
  | "pmpcfg12" => (some 0x3AC#12)
  | "pmpcfg13" => (some 0x3AD#12)
  | "pmpcfg14" => (some 0x3AE#12)
  | "pmpcfg15" => (some 0x3AF#12)
  | "pmpaddr0" => (some 0x3B0#12)
  | "pmpaddr1" => (some 0x3B1#12)
  | "pmpaddr2" => (some 0x3B2#12)
  | "pmpaddr3" => (some 0x3B3#12)
  | "pmpaddr4" => (some 0x3B4#12)
  | "pmpaddr5" => (some 0x3B5#12)
  | "pmpaddr6" => (some 0x3B6#12)
  | "pmpaddr7" => (some 0x3B7#12)
  | "pmpaddr8" => (some 0x3B8#12)
  | "pmpaddr9" => (some 0x3B9#12)
  | "pmpaddr10" => (some 0x3BA#12)
  | "pmpaddr11" => (some 0x3BB#12)
  | "pmpaddr12" => (some 0x3BC#12)
  | "pmpaddr13" => (some 0x3BD#12)
  | "pmpaddr14" => (some 0x3BE#12)
  | "pmpaddr15" => (some 0x3BF#12)
  | "pmpaddr16" => (some 0x3C0#12)
  | "pmpaddr17" => (some 0x3C1#12)
  | "pmpaddr18" => (some 0x3C2#12)
  | "pmpaddr19" => (some 0x3C3#12)
  | "pmpaddr20" => (some 0x3C4#12)
  | "pmpaddr21" => (some 0x3C5#12)
  | "pmpaddr22" => (some 0x3C6#12)
  | "pmpaddr23" => (some 0x3C7#12)
  | "pmpaddr24" => (some 0x3C8#12)
  | "pmpaddr25" => (some 0x3C9#12)
  | "pmpaddr26" => (some 0x3CA#12)
  | "pmpaddr27" => (some 0x3CB#12)
  | "pmpaddr28" => (some 0x3CC#12)
  | "pmpaddr29" => (some 0x3CD#12)
  | "pmpaddr30" => (some 0x3CE#12)
  | "pmpaddr31" => (some 0x3CF#12)
  | "pmpaddr32" => (some 0x3D0#12)
  | "pmpaddr33" => (some 0x3D1#12)
  | "pmpaddr34" => (some 0x3D2#12)
  | "pmpaddr35" => (some 0x3D3#12)
  | "pmpaddr36" => (some 0x3D4#12)
  | "pmpaddr37" => (some 0x3D5#12)
  | "pmpaddr38" => (some 0x3D6#12)
  | "pmpaddr39" => (some 0x3D7#12)
  | "pmpaddr40" => (some 0x3D8#12)
  | "pmpaddr41" => (some 0x3D9#12)
  | "pmpaddr42" => (some 0x3DA#12)
  | "pmpaddr43" => (some 0x3DB#12)
  | "pmpaddr44" => (some 0x3DC#12)
  | "pmpaddr45" => (some 0x3DD#12)
  | "pmpaddr46" => (some 0x3DE#12)
  | "pmpaddr47" => (some 0x3DF#12)
  | "pmpaddr48" => (some 0x3E0#12)
  | "pmpaddr49" => (some 0x3E1#12)
  | "pmpaddr50" => (some 0x3E2#12)
  | "pmpaddr51" => (some 0x3E3#12)
  | "pmpaddr52" => (some 0x3E4#12)
  | "pmpaddr53" => (some 0x3E5#12)
  | "pmpaddr54" => (some 0x3E6#12)
  | "pmpaddr55" => (some 0x3E7#12)
  | "pmpaddr56" => (some 0x3E8#12)
  | "pmpaddr57" => (some 0x3E9#12)
  | "pmpaddr58" => (some 0x3EA#12)
  | "pmpaddr59" => (some 0x3EB#12)
  | "pmpaddr60" => (some 0x3EC#12)
  | "pmpaddr61" => (some 0x3ED#12)
  | "pmpaddr62" => (some 0x3EE#12)
  | "pmpaddr63" => (some 0x3EF#12)
  | "fflags" => (some 0x001#12)
  | "frm" => (some 0x002#12)
  | "fcsr" => (some 0x003#12)
  | "vstart" => (some 0x008#12)
  | "vxsat" => (some 0x009#12)
  | "vxrm" => (some 0x00A#12)
  | "vcsr" => (some 0x00F#12)
  | "vl" => (some 0xC20#12)
  | "vtype" => (some 0xC21#12)
  | "vlenb" => (some 0xC22#12)
  | "mcyclecfg" => (some 0x321#12)
  | "mcyclecfgh" => (some 0x721#12)
  | "minstretcfg" => (some 0x322#12)
  | "minstretcfgh" => (some 0x722#12)
  | "satp" => (some 0x180#12)
  | "seed" => (some 0x015#12)
  | "hpmcounter3" => (some 0xC03#12)
  | "hpmcounter4" => (some 0xC04#12)
  | "hpmcounter5" => (some 0xC05#12)
  | "hpmcounter6" => (some 0xC06#12)
  | "hpmcounter7" => (some 0xC07#12)
  | "hpmcounter8" => (some 0xC08#12)
  | "hpmcounter9" => (some 0xC09#12)
  | "hpmcounter10" => (some 0xC0A#12)
  | "hpmcounter11" => (some 0xC0B#12)
  | "hpmcounter12" => (some 0xC0C#12)
  | "hpmcounter13" => (some 0xC0D#12)
  | "hpmcounter14" => (some 0xC0E#12)
  | "hpmcounter15" => (some 0xC0F#12)
  | "hpmcounter16" => (some 0xC10#12)
  | "hpmcounter17" => (some 0xC11#12)
  | "hpmcounter18" => (some 0xC12#12)
  | "hpmcounter19" => (some 0xC13#12)
  | "hpmcounter20" => (some 0xC14#12)
  | "hpmcounter21" => (some 0xC15#12)
  | "hpmcounter22" => (some 0xC16#12)
  | "hpmcounter23" => (some 0xC17#12)
  | "hpmcounter24" => (some 0xC18#12)
  | "hpmcounter25" => (some 0xC19#12)
  | "hpmcounter26" => (some 0xC1A#12)
  | "hpmcounter27" => (some 0xC1B#12)
  | "hpmcounter28" => (some 0xC1C#12)
  | "hpmcounter29" => (some 0xC1D#12)
  | "hpmcounter30" => (some 0xC1E#12)
  | "hpmcounter31" => (some 0xC1F#12)
  | "hpmcounter3h" => (some 0xC83#12)
  | "hpmcounter4h" => (some 0xC84#12)
  | "hpmcounter5h" => (some 0xC85#12)
  | "hpmcounter6h" => (some 0xC86#12)
  | "hpmcounter7h" => (some 0xC87#12)
  | "hpmcounter8h" => (some 0xC88#12)
  | "hpmcounter9h" => (some 0xC89#12)
  | "hpmcounter10h" => (some 0xC8A#12)
  | "hpmcounter11h" => (some 0xC8B#12)
  | "hpmcounter12h" => (some 0xC8C#12)
  | "hpmcounter13h" => (some 0xC8D#12)
  | "hpmcounter14h" => (some 0xC8E#12)
  | "hpmcounter15h" => (some 0xC8F#12)
  | "hpmcounter16h" => (some 0xC90#12)
  | "hpmcounter17h" => (some 0xC91#12)
  | "hpmcounter18h" => (some 0xC92#12)
  | "hpmcounter19h" => (some 0xC93#12)
  | "hpmcounter20h" => (some 0xC94#12)
  | "hpmcounter21h" => (some 0xC95#12)
  | "hpmcounter22h" => (some 0xC96#12)
  | "hpmcounter23h" => (some 0xC97#12)
  | "hpmcounter24h" => (some 0xC98#12)
  | "hpmcounter25h" => (some 0xC99#12)
  | "hpmcounter26h" => (some 0xC9A#12)
  | "hpmcounter27h" => (some 0xC9B#12)
  | "hpmcounter28h" => (some 0xC9C#12)
  | "hpmcounter29h" => (some 0xC9D#12)
  | "hpmcounter30h" => (some 0xC9E#12)
  | "hpmcounter31h" => (some 0xC9F#12)
  | "mhpmevent3" => (some 0x323#12)
  | "mhpmevent4" => (some 0x324#12)
  | "mhpmevent5" => (some 0x325#12)
  | "mhpmevent6" => (some 0x326#12)
  | "mhpmevent7" => (some 0x327#12)
  | "mhpmevent8" => (some 0x328#12)
  | "mhpmevent9" => (some 0x329#12)
  | "mhpmevent10" => (some 0x32A#12)
  | "mhpmevent11" => (some 0x32B#12)
  | "mhpmevent12" => (some 0x32C#12)
  | "mhpmevent13" => (some 0x32D#12)
  | "mhpmevent14" => (some 0x32E#12)
  | "mhpmevent15" => (some 0x32F#12)
  | "mhpmevent16" => (some 0x330#12)
  | "mhpmevent17" => (some 0x331#12)
  | "mhpmevent18" => (some 0x332#12)
  | "mhpmevent19" => (some 0x333#12)
  | "mhpmevent20" => (some 0x334#12)
  | "mhpmevent21" => (some 0x335#12)
  | "mhpmevent22" => (some 0x336#12)
  | "mhpmevent23" => (some 0x337#12)
  | "mhpmevent24" => (some 0x338#12)
  | "mhpmevent25" => (some 0x339#12)
  | "mhpmevent26" => (some 0x33A#12)
  | "mhpmevent27" => (some 0x33B#12)
  | "mhpmevent28" => (some 0x33C#12)
  | "mhpmevent29" => (some 0x33D#12)
  | "mhpmevent30" => (some 0x33E#12)
  | "mhpmevent31" => (some 0x33F#12)
  | "mhpmcounter3" => (some 0xB03#12)
  | "mhpmcounter4" => (some 0xB04#12)
  | "mhpmcounter5" => (some 0xB05#12)
  | "mhpmcounter6" => (some 0xB06#12)
  | "mhpmcounter7" => (some 0xB07#12)
  | "mhpmcounter8" => (some 0xB08#12)
  | "mhpmcounter9" => (some 0xB09#12)
  | "mhpmcounter10" => (some 0xB0A#12)
  | "mhpmcounter11" => (some 0xB0B#12)
  | "mhpmcounter12" => (some 0xB0C#12)
  | "mhpmcounter13" => (some 0xB0D#12)
  | "mhpmcounter14" => (some 0xB0E#12)
  | "mhpmcounter15" => (some 0xB0F#12)
  | "mhpmcounter16" => (some 0xB10#12)
  | "mhpmcounter17" => (some 0xB11#12)
  | "mhpmcounter18" => (some 0xB12#12)
  | "mhpmcounter19" => (some 0xB13#12)
  | "mhpmcounter20" => (some 0xB14#12)
  | "mhpmcounter21" => (some 0xB15#12)
  | "mhpmcounter22" => (some 0xB16#12)
  | "mhpmcounter23" => (some 0xB17#12)
  | "mhpmcounter24" => (some 0xB18#12)
  | "mhpmcounter25" => (some 0xB19#12)
  | "mhpmcounter26" => (some 0xB1A#12)
  | "mhpmcounter27" => (some 0xB1B#12)
  | "mhpmcounter28" => (some 0xB1C#12)
  | "mhpmcounter29" => (some 0xB1D#12)
  | "mhpmcounter30" => (some 0xB1E#12)
  | "mhpmcounter31" => (some 0xB1F#12)
  | "mhpmcounter3h" => (some 0xB83#12)
  | "mhpmcounter4h" => (some 0xB84#12)
  | "mhpmcounter5h" => (some 0xB85#12)
  | "mhpmcounter6h" => (some 0xB86#12)
  | "mhpmcounter7h" => (some 0xB87#12)
  | "mhpmcounter8h" => (some 0xB88#12)
  | "mhpmcounter9h" => (some 0xB89#12)
  | "mhpmcounter10h" => (some 0xB8A#12)
  | "mhpmcounter11h" => (some 0xB8B#12)
  | "mhpmcounter12h" => (some 0xB8C#12)
  | "mhpmcounter13h" => (some 0xB8D#12)
  | "mhpmcounter14h" => (some 0xB8E#12)
  | "mhpmcounter15h" => (some 0xB8F#12)
  | "mhpmcounter16h" => (some 0xB90#12)
  | "mhpmcounter17h" => (some 0xB91#12)
  | "mhpmcounter18h" => (some 0xB92#12)
  | "mhpmcounter19h" => (some 0xB93#12)
  | "mhpmcounter20h" => (some 0xB94#12)
  | "mhpmcounter21h" => (some 0xB95#12)
  | "mhpmcounter22h" => (some 0xB96#12)
  | "mhpmcounter23h" => (some 0xB97#12)
  | "mhpmcounter24h" => (some 0xB98#12)
  | "mhpmcounter25h" => (some 0xB99#12)
  | "mhpmcounter26h" => (some 0xB9A#12)
  | "mhpmcounter27h" => (some 0xB9B#12)
  | "mhpmcounter28h" => (some 0xB9C#12)
  | "mhpmcounter29h" => (some 0xB9D#12)
  | "mhpmcounter30h" => (some 0xB9E#12)
  | "mhpmcounter31h" => (some 0xB9F#12)
  | "mhpmevent3h" => (some 0x723#12)
  | "mhpmevent4h" => (some 0x724#12)
  | "mhpmevent5h" => (some 0x725#12)
  | "mhpmevent6h" => (some 0x726#12)
  | "mhpmevent7h" => (some 0x727#12)
  | "mhpmevent8h" => (some 0x728#12)
  | "mhpmevent9h" => (some 0x729#12)
  | "mhpmevent10h" => (some 0x72A#12)
  | "mhpmevent11h" => (some 0x72B#12)
  | "mhpmevent12h" => (some 0x72C#12)
  | "mhpmevent13h" => (some 0x72D#12)
  | "mhpmevent14h" => (some 0x72E#12)
  | "mhpmevent15h" => (some 0x72F#12)
  | "mhpmevent16h" => (some 0x730#12)
  | "mhpmevent17h" => (some 0x731#12)
  | "mhpmevent18h" => (some 0x732#12)
  | "mhpmevent19h" => (some 0x733#12)
  | "mhpmevent20h" => (some 0x734#12)
  | "mhpmevent21h" => (some 0x735#12)
  | "mhpmevent22h" => (some 0x736#12)
  | "mhpmevent23h" => (some 0x737#12)
  | "mhpmevent24h" => (some 0x738#12)
  | "mhpmevent25h" => (some 0x739#12)
  | "mhpmevent26h" => (some 0x73A#12)
  | "mhpmevent27h" => (some 0x73B#12)
  | "mhpmevent28h" => (some 0x73C#12)
  | "mhpmevent29h" => (some 0x73D#12)
  | "mhpmevent30h" => (some 0x73E#12)
  | "mhpmevent31h" => (some 0x73F#12)
  | "scountovf" => (some 0xDA0#12)
  | "stimecmp" => (some 0x14D#12)
  | "stimecmph" => (some 0x15D#12)
  | "cycle" => (some 0xC00#12)
  | "time" => (some 0xC01#12)
  | "instret" => (some 0xC02#12)
  | "cycleh" => (some 0xC80#12)
  | "timeh" => (some 0xC81#12)
  | "instreth" => (some 0xC82#12)
  | "mcycle" => (some 0xB00#12)
  | "minstret" => (some 0xB02#12)
  | "mcycleh" => (some 0xB80#12)
  | "minstreth" => (some 0xB82#12)
  | mapping0_ =>
    (if ((hex_bits_12_backwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_12_backwards mapping0_) with
      | reg => (some reg))
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def csr_name_write_callback (name : String) (value : (BitVec 64)) : SailM Unit := do
  let csr ← do (csr_name_map_backwards name)
  (pure (csr_full_write_callback name csr value))

def csr_id_write_callback (csr : (BitVec 12)) (value : (BitVec 64)) : SailM Unit := do
  let name ← do (csr_name_map_forwards csr)
  (pure (csr_full_write_callback name csr value))

def csr_name_read_callback (name : String) (value : (BitVec 64)) : SailM Unit := do
  let csr ← do (csr_name_map_backwards name)
  (pure (csr_full_read_callback name csr value))

def csr_id_read_callback (csr : (BitVec 12)) (value : (BitVec 64)) : SailM Unit := do
  let name ← do (csr_name_map_forwards csr)
  (pure (csr_full_read_callback name csr value))

def long_csr_write_callback (name : String) (name_high : String) (value : (BitVec 64)) : SailM Unit := do
  (csr_name_write_callback name (Sail.BitVec.extractLsb value (xlen -i 1) 0))

