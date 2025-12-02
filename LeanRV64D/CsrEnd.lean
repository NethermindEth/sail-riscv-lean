import LeanRV64D.HexBits

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

def csr_name_map_forwards_matches (arg_ : (BitVec 12)) : Bool :=
  match arg_ with
  | 0x301 => true
  | 0x300 => true
  | 0x310 => true
  | 0x747 => true
  | 0x757 => true
  | 0x30A => true
  | 0x31A => true
  | 0x10A => true
  | 0x304 => true
  | 0x344 => true
  | 0x302 => true
  | 0x312 => true
  | 0x303 => true
  | 0x342 => true
  | 0x343 => true
  | 0x340 => true
  | 0x106 => true
  | 0x306 => true
  | 0x320 => true
  | 0xF11 => true
  | 0xF12 => true
  | 0xF13 => true
  | 0xF14 => true
  | 0xF15 => true
  | 0x100 => true
  | 0x144 => true
  | 0x104 => true
  | 0x140 => true
  | 0x142 => true
  | 0x143 => true
  | 0x7A0 => true
  | 0x7A1 => true
  | 0x7A2 => true
  | 0x7A3 => true
  | 0x105 => true
  | 0x141 => true
  | 0x305 => true
  | 0x341 => true
  | 0x3A0 => true
  | 0x3A1 => true
  | 0x3A2 => true
  | 0x3A3 => true
  | 0x3A4 => true
  | 0x3A5 => true
  | 0x3A6 => true
  | 0x3A7 => true
  | 0x3A8 => true
  | 0x3A9 => true
  | 0x3AA => true
  | 0x3AB => true
  | 0x3AC => true
  | 0x3AD => true
  | 0x3AE => true
  | 0x3AF => true
  | 0x3B0 => true
  | 0x3B1 => true
  | 0x3B2 => true
  | 0x3B3 => true
  | 0x3B4 => true
  | 0x3B5 => true
  | 0x3B6 => true
  | 0x3B7 => true
  | 0x3B8 => true
  | 0x3B9 => true
  | 0x3BA => true
  | 0x3BB => true
  | 0x3BC => true
  | 0x3BD => true
  | 0x3BE => true
  | 0x3BF => true
  | 0x3C0 => true
  | 0x3C1 => true
  | 0x3C2 => true
  | 0x3C3 => true
  | 0x3C4 => true
  | 0x3C5 => true
  | 0x3C6 => true
  | 0x3C7 => true
  | 0x3C8 => true
  | 0x3C9 => true
  | 0x3CA => true
  | 0x3CB => true
  | 0x3CC => true
  | 0x3CD => true
  | 0x3CE => true
  | 0x3CF => true
  | 0x3D0 => true
  | 0x3D1 => true
  | 0x3D2 => true
  | 0x3D3 => true
  | 0x3D4 => true
  | 0x3D5 => true
  | 0x3D6 => true
  | 0x3D7 => true
  | 0x3D8 => true
  | 0x3D9 => true
  | 0x3DA => true
  | 0x3DB => true
  | 0x3DC => true
  | 0x3DD => true
  | 0x3DE => true
  | 0x3DF => true
  | 0x3E0 => true
  | 0x3E1 => true
  | 0x3E2 => true
  | 0x3E3 => true
  | 0x3E4 => true
  | 0x3E5 => true
  | 0x3E6 => true
  | 0x3E7 => true
  | 0x3E8 => true
  | 0x3E9 => true
  | 0x3EA => true
  | 0x3EB => true
  | 0x3EC => true
  | 0x3ED => true
  | 0x3EE => true
  | 0x3EF => true
  | 0x001 => true
  | 0x002 => true
  | 0x003 => true
  | 0x008 => true
  | 0x009 => true
  | 0x00A => true
  | 0x00F => true
  | 0xC20 => true
  | 0xC21 => true
  | 0xC22 => true
  | 0x321 => true
  | 0x721 => true
  | 0x322 => true
  | 0x722 => true
  | 0x180 => true
  | 0x015 => true
  | 0xC03 => true
  | 0xC04 => true
  | 0xC05 => true
  | 0xC06 => true
  | 0xC07 => true
  | 0xC08 => true
  | 0xC09 => true
  | 0xC0A => true
  | 0xC0B => true
  | 0xC0C => true
  | 0xC0D => true
  | 0xC0E => true
  | 0xC0F => true
  | 0xC10 => true
  | 0xC11 => true
  | 0xC12 => true
  | 0xC13 => true
  | 0xC14 => true
  | 0xC15 => true
  | 0xC16 => true
  | 0xC17 => true
  | 0xC18 => true
  | 0xC19 => true
  | 0xC1A => true
  | 0xC1B => true
  | 0xC1C => true
  | 0xC1D => true
  | 0xC1E => true
  | 0xC1F => true
  | 0xC83 => true
  | 0xC84 => true
  | 0xC85 => true
  | 0xC86 => true
  | 0xC87 => true
  | 0xC88 => true
  | 0xC89 => true
  | 0xC8A => true
  | 0xC8B => true
  | 0xC8C => true
  | 0xC8D => true
  | 0xC8E => true
  | 0xC8F => true
  | 0xC90 => true
  | 0xC91 => true
  | 0xC92 => true
  | 0xC93 => true
  | 0xC94 => true
  | 0xC95 => true
  | 0xC96 => true
  | 0xC97 => true
  | 0xC98 => true
  | 0xC99 => true
  | 0xC9A => true
  | 0xC9B => true
  | 0xC9C => true
  | 0xC9D => true
  | 0xC9E => true
  | 0xC9F => true
  | 0x323 => true
  | 0x324 => true
  | 0x325 => true
  | 0x326 => true
  | 0x327 => true
  | 0x328 => true
  | 0x329 => true
  | 0x32A => true
  | 0x32B => true
  | 0x32C => true
  | 0x32D => true
  | 0x32E => true
  | 0x32F => true
  | 0x330 => true
  | 0x331 => true
  | 0x332 => true
  | 0x333 => true
  | 0x334 => true
  | 0x335 => true
  | 0x336 => true
  | 0x337 => true
  | 0x338 => true
  | 0x339 => true
  | 0x33A => true
  | 0x33B => true
  | 0x33C => true
  | 0x33D => true
  | 0x33E => true
  | 0x33F => true
  | 0xB03 => true
  | 0xB04 => true
  | 0xB05 => true
  | 0xB06 => true
  | 0xB07 => true
  | 0xB08 => true
  | 0xB09 => true
  | 0xB0A => true
  | 0xB0B => true
  | 0xB0C => true
  | 0xB0D => true
  | 0xB0E => true
  | 0xB0F => true
  | 0xB10 => true
  | 0xB11 => true
  | 0xB12 => true
  | 0xB13 => true
  | 0xB14 => true
  | 0xB15 => true
  | 0xB16 => true
  | 0xB17 => true
  | 0xB18 => true
  | 0xB19 => true
  | 0xB1A => true
  | 0xB1B => true
  | 0xB1C => true
  | 0xB1D => true
  | 0xB1E => true
  | 0xB1F => true
  | 0xB83 => true
  | 0xB84 => true
  | 0xB85 => true
  | 0xB86 => true
  | 0xB87 => true
  | 0xB88 => true
  | 0xB89 => true
  | 0xB8A => true
  | 0xB8B => true
  | 0xB8C => true
  | 0xB8D => true
  | 0xB8E => true
  | 0xB8F => true
  | 0xB90 => true
  | 0xB91 => true
  | 0xB92 => true
  | 0xB93 => true
  | 0xB94 => true
  | 0xB95 => true
  | 0xB96 => true
  | 0xB97 => true
  | 0xB98 => true
  | 0xB99 => true
  | 0xB9A => true
  | 0xB9B => true
  | 0xB9C => true
  | 0xB9D => true
  | 0xB9E => true
  | 0xB9F => true
  | 0x723 => true
  | 0x724 => true
  | 0x725 => true
  | 0x726 => true
  | 0x727 => true
  | 0x728 => true
  | 0x729 => true
  | 0x72A => true
  | 0x72B => true
  | 0x72C => true
  | 0x72D => true
  | 0x72E => true
  | 0x72F => true
  | 0x730 => true
  | 0x731 => true
  | 0x732 => true
  | 0x733 => true
  | 0x734 => true
  | 0x735 => true
  | 0x736 => true
  | 0x737 => true
  | 0x738 => true
  | 0x739 => true
  | 0x73A => true
  | 0x73B => true
  | 0x73C => true
  | 0x73D => true
  | 0x73E => true
  | 0x73F => true
  | 0xDA0 => true
  | 0x14D => true
  | 0x15D => true
  | 0xC00 => true
  | 0xC01 => true
  | 0xC02 => true
  | 0xC80 => true
  | 0xC81 => true
  | 0xC82 => true
  | 0xB00 => true
  | 0xB02 => true
  | 0xB80 => true
  | 0xB82 => true
  | reg => true

def csr_name_map_backwards_matches (arg_ : String) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | "misa" => (some true)
  | "mstatus" => (some true)
  | "mstatush" => (some true)
  | "mseccfg" => (some true)
  | "mseccfgh" => (some true)
  | "menvcfg" => (some true)
  | "menvcfgh" => (some true)
  | "senvcfg" => (some true)
  | "mie" => (some true)
  | "mip" => (some true)
  | "medeleg" => (some true)
  | "medelegh" => (some true)
  | "mideleg" => (some true)
  | "mcause" => (some true)
  | "mtval" => (some true)
  | "mscratch" => (some true)
  | "scounteren" => (some true)
  | "mcounteren" => (some true)
  | "mcountinhibit" => (some true)
  | "mvendorid" => (some true)
  | "marchid" => (some true)
  | "mimpid" => (some true)
  | "mhartid" => (some true)
  | "mconfigptr" => (some true)
  | "sstatus" => (some true)
  | "sip" => (some true)
  | "sie" => (some true)
  | "sscratch" => (some true)
  | "scause" => (some true)
  | "stval" => (some true)
  | "tselect" => (some true)
  | "tdata1" => (some true)
  | "tdata2" => (some true)
  | "tdata3" => (some true)
  | "stvec" => (some true)
  | "sepc" => (some true)
  | "mtvec" => (some true)
  | "mepc" => (some true)
  | "pmpcfg0" => (some true)
  | "pmpcfg1" => (some true)
  | "pmpcfg2" => (some true)
  | "pmpcfg3" => (some true)
  | "pmpcfg4" => (some true)
  | "pmpcfg5" => (some true)
  | "pmpcfg6" => (some true)
  | "pmpcfg7" => (some true)
  | "pmpcfg8" => (some true)
  | "pmpcfg9" => (some true)
  | "pmpcfg10" => (some true)
  | "pmpcfg11" => (some true)
  | "pmpcfg12" => (some true)
  | "pmpcfg13" => (some true)
  | "pmpcfg14" => (some true)
  | "pmpcfg15" => (some true)
  | "pmpaddr0" => (some true)
  | "pmpaddr1" => (some true)
  | "pmpaddr2" => (some true)
  | "pmpaddr3" => (some true)
  | "pmpaddr4" => (some true)
  | "pmpaddr5" => (some true)
  | "pmpaddr6" => (some true)
  | "pmpaddr7" => (some true)
  | "pmpaddr8" => (some true)
  | "pmpaddr9" => (some true)
  | "pmpaddr10" => (some true)
  | "pmpaddr11" => (some true)
  | "pmpaddr12" => (some true)
  | "pmpaddr13" => (some true)
  | "pmpaddr14" => (some true)
  | "pmpaddr15" => (some true)
  | "pmpaddr16" => (some true)
  | "pmpaddr17" => (some true)
  | "pmpaddr18" => (some true)
  | "pmpaddr19" => (some true)
  | "pmpaddr20" => (some true)
  | "pmpaddr21" => (some true)
  | "pmpaddr22" => (some true)
  | "pmpaddr23" => (some true)
  | "pmpaddr24" => (some true)
  | "pmpaddr25" => (some true)
  | "pmpaddr26" => (some true)
  | "pmpaddr27" => (some true)
  | "pmpaddr28" => (some true)
  | "pmpaddr29" => (some true)
  | "pmpaddr30" => (some true)
  | "pmpaddr31" => (some true)
  | "pmpaddr32" => (some true)
  | "pmpaddr33" => (some true)
  | "pmpaddr34" => (some true)
  | "pmpaddr35" => (some true)
  | "pmpaddr36" => (some true)
  | "pmpaddr37" => (some true)
  | "pmpaddr38" => (some true)
  | "pmpaddr39" => (some true)
  | "pmpaddr40" => (some true)
  | "pmpaddr41" => (some true)
  | "pmpaddr42" => (some true)
  | "pmpaddr43" => (some true)
  | "pmpaddr44" => (some true)
  | "pmpaddr45" => (some true)
  | "pmpaddr46" => (some true)
  | "pmpaddr47" => (some true)
  | "pmpaddr48" => (some true)
  | "pmpaddr49" => (some true)
  | "pmpaddr50" => (some true)
  | "pmpaddr51" => (some true)
  | "pmpaddr52" => (some true)
  | "pmpaddr53" => (some true)
  | "pmpaddr54" => (some true)
  | "pmpaddr55" => (some true)
  | "pmpaddr56" => (some true)
  | "pmpaddr57" => (some true)
  | "pmpaddr58" => (some true)
  | "pmpaddr59" => (some true)
  | "pmpaddr60" => (some true)
  | "pmpaddr61" => (some true)
  | "pmpaddr62" => (some true)
  | "pmpaddr63" => (some true)
  | "fflags" => (some true)
  | "frm" => (some true)
  | "fcsr" => (some true)
  | "vstart" => (some true)
  | "vxsat" => (some true)
  | "vxrm" => (some true)
  | "vcsr" => (some true)
  | "vl" => (some true)
  | "vtype" => (some true)
  | "vlenb" => (some true)
  | "mcyclecfg" => (some true)
  | "mcyclecfgh" => (some true)
  | "minstretcfg" => (some true)
  | "minstretcfgh" => (some true)
  | "satp" => (some true)
  | "seed" => (some true)
  | "hpmcounter3" => (some true)
  | "hpmcounter4" => (some true)
  | "hpmcounter5" => (some true)
  | "hpmcounter6" => (some true)
  | "hpmcounter7" => (some true)
  | "hpmcounter8" => (some true)
  | "hpmcounter9" => (some true)
  | "hpmcounter10" => (some true)
  | "hpmcounter11" => (some true)
  | "hpmcounter12" => (some true)
  | "hpmcounter13" => (some true)
  | "hpmcounter14" => (some true)
  | "hpmcounter15" => (some true)
  | "hpmcounter16" => (some true)
  | "hpmcounter17" => (some true)
  | "hpmcounter18" => (some true)
  | "hpmcounter19" => (some true)
  | "hpmcounter20" => (some true)
  | "hpmcounter21" => (some true)
  | "hpmcounter22" => (some true)
  | "hpmcounter23" => (some true)
  | "hpmcounter24" => (some true)
  | "hpmcounter25" => (some true)
  | "hpmcounter26" => (some true)
  | "hpmcounter27" => (some true)
  | "hpmcounter28" => (some true)
  | "hpmcounter29" => (some true)
  | "hpmcounter30" => (some true)
  | "hpmcounter31" => (some true)
  | "hpmcounter3h" => (some true)
  | "hpmcounter4h" => (some true)
  | "hpmcounter5h" => (some true)
  | "hpmcounter6h" => (some true)
  | "hpmcounter7h" => (some true)
  | "hpmcounter8h" => (some true)
  | "hpmcounter9h" => (some true)
  | "hpmcounter10h" => (some true)
  | "hpmcounter11h" => (some true)
  | "hpmcounter12h" => (some true)
  | "hpmcounter13h" => (some true)
  | "hpmcounter14h" => (some true)
  | "hpmcounter15h" => (some true)
  | "hpmcounter16h" => (some true)
  | "hpmcounter17h" => (some true)
  | "hpmcounter18h" => (some true)
  | "hpmcounter19h" => (some true)
  | "hpmcounter20h" => (some true)
  | "hpmcounter21h" => (some true)
  | "hpmcounter22h" => (some true)
  | "hpmcounter23h" => (some true)
  | "hpmcounter24h" => (some true)
  | "hpmcounter25h" => (some true)
  | "hpmcounter26h" => (some true)
  | "hpmcounter27h" => (some true)
  | "hpmcounter28h" => (some true)
  | "hpmcounter29h" => (some true)
  | "hpmcounter30h" => (some true)
  | "hpmcounter31h" => (some true)
  | "mhpmevent3" => (some true)
  | "mhpmevent4" => (some true)
  | "mhpmevent5" => (some true)
  | "mhpmevent6" => (some true)
  | "mhpmevent7" => (some true)
  | "mhpmevent8" => (some true)
  | "mhpmevent9" => (some true)
  | "mhpmevent10" => (some true)
  | "mhpmevent11" => (some true)
  | "mhpmevent12" => (some true)
  | "mhpmevent13" => (some true)
  | "mhpmevent14" => (some true)
  | "mhpmevent15" => (some true)
  | "mhpmevent16" => (some true)
  | "mhpmevent17" => (some true)
  | "mhpmevent18" => (some true)
  | "mhpmevent19" => (some true)
  | "mhpmevent20" => (some true)
  | "mhpmevent21" => (some true)
  | "mhpmevent22" => (some true)
  | "mhpmevent23" => (some true)
  | "mhpmevent24" => (some true)
  | "mhpmevent25" => (some true)
  | "mhpmevent26" => (some true)
  | "mhpmevent27" => (some true)
  | "mhpmevent28" => (some true)
  | "mhpmevent29" => (some true)
  | "mhpmevent30" => (some true)
  | "mhpmevent31" => (some true)
  | "mhpmcounter3" => (some true)
  | "mhpmcounter4" => (some true)
  | "mhpmcounter5" => (some true)
  | "mhpmcounter6" => (some true)
  | "mhpmcounter7" => (some true)
  | "mhpmcounter8" => (some true)
  | "mhpmcounter9" => (some true)
  | "mhpmcounter10" => (some true)
  | "mhpmcounter11" => (some true)
  | "mhpmcounter12" => (some true)
  | "mhpmcounter13" => (some true)
  | "mhpmcounter14" => (some true)
  | "mhpmcounter15" => (some true)
  | "mhpmcounter16" => (some true)
  | "mhpmcounter17" => (some true)
  | "mhpmcounter18" => (some true)
  | "mhpmcounter19" => (some true)
  | "mhpmcounter20" => (some true)
  | "mhpmcounter21" => (some true)
  | "mhpmcounter22" => (some true)
  | "mhpmcounter23" => (some true)
  | "mhpmcounter24" => (some true)
  | "mhpmcounter25" => (some true)
  | "mhpmcounter26" => (some true)
  | "mhpmcounter27" => (some true)
  | "mhpmcounter28" => (some true)
  | "mhpmcounter29" => (some true)
  | "mhpmcounter30" => (some true)
  | "mhpmcounter31" => (some true)
  | "mhpmcounter3h" => (some true)
  | "mhpmcounter4h" => (some true)
  | "mhpmcounter5h" => (some true)
  | "mhpmcounter6h" => (some true)
  | "mhpmcounter7h" => (some true)
  | "mhpmcounter8h" => (some true)
  | "mhpmcounter9h" => (some true)
  | "mhpmcounter10h" => (some true)
  | "mhpmcounter11h" => (some true)
  | "mhpmcounter12h" => (some true)
  | "mhpmcounter13h" => (some true)
  | "mhpmcounter14h" => (some true)
  | "mhpmcounter15h" => (some true)
  | "mhpmcounter16h" => (some true)
  | "mhpmcounter17h" => (some true)
  | "mhpmcounter18h" => (some true)
  | "mhpmcounter19h" => (some true)
  | "mhpmcounter20h" => (some true)
  | "mhpmcounter21h" => (some true)
  | "mhpmcounter22h" => (some true)
  | "mhpmcounter23h" => (some true)
  | "mhpmcounter24h" => (some true)
  | "mhpmcounter25h" => (some true)
  | "mhpmcounter26h" => (some true)
  | "mhpmcounter27h" => (some true)
  | "mhpmcounter28h" => (some true)
  | "mhpmcounter29h" => (some true)
  | "mhpmcounter30h" => (some true)
  | "mhpmcounter31h" => (some true)
  | "mhpmevent3h" => (some true)
  | "mhpmevent4h" => (some true)
  | "mhpmevent5h" => (some true)
  | "mhpmevent6h" => (some true)
  | "mhpmevent7h" => (some true)
  | "mhpmevent8h" => (some true)
  | "mhpmevent9h" => (some true)
  | "mhpmevent10h" => (some true)
  | "mhpmevent11h" => (some true)
  | "mhpmevent12h" => (some true)
  | "mhpmevent13h" => (some true)
  | "mhpmevent14h" => (some true)
  | "mhpmevent15h" => (some true)
  | "mhpmevent16h" => (some true)
  | "mhpmevent17h" => (some true)
  | "mhpmevent18h" => (some true)
  | "mhpmevent19h" => (some true)
  | "mhpmevent20h" => (some true)
  | "mhpmevent21h" => (some true)
  | "mhpmevent22h" => (some true)
  | "mhpmevent23h" => (some true)
  | "mhpmevent24h" => (some true)
  | "mhpmevent25h" => (some true)
  | "mhpmevent26h" => (some true)
  | "mhpmevent27h" => (some true)
  | "mhpmevent28h" => (some true)
  | "mhpmevent29h" => (some true)
  | "mhpmevent30h" => (some true)
  | "mhpmevent31h" => (some true)
  | "scountovf" => (some true)
  | "stimecmp" => (some true)
  | "stimecmph" => (some true)
  | "cycle" => (some true)
  | "time" => (some true)
  | "instret" => (some true)
  | "cycleh" => (some true)
  | "timeh" => (some true)
  | "instreth" => (some true)
  | "mcycle" => (some true)
  | "minstret" => (some true)
  | "mcycleh" => (some true)
  | "minstreth" => (some true)
  | mapping0_ =>
    (if ((hex_bits_12_backwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_12_backwards mapping0_) with
      | reg => (some true))
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

