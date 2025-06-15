import LeanRV64D.Prelude
import LeanRV64D.RiscvXlen
import LeanRV64D.RiscvExtensions
import LeanRV64D.RiscvPlatform

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

noncomputable section

namespace LeanRV64D.Functions

open zvkfunct6
open zvk_vaesem_funct6
open zvk_vaesef_funct6
open zvk_vaesdm_funct6
open zvk_vaesdf_funct6
open zicondop
open wxfunct6
open wvxfunct6
open wvvfunct6
open wvfunct6
open wrsop
open write_kind
open word_width
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
open vext8funct6
open vext4funct6
open vext2funct6
open uop
open sopw
open sop
open seed_opst
open rounding_mode
open ropw
open rop
open rmvvfunct6
open rivvfunct6
open rfvvfunct6
open regno
open regidx
open read_kind
open pmpAddrMatch
open physaddr
open option
open nxsfunct6
open nxfunct6
open nvsfunct6
open nvfunct6
open nisfunct6
open nifunct6
open mvxmafunct6
open mvxfunct6
open mvvmafunct6
open mvvfunct6
open mmfunct6
open maskfunct3
open iop
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
open cbop_zicbom
open cbie
open bropw_zbb
open bropw_zba
open brop_zbs
open brop_zbkb
open brop_zbb
open brop_zba
open bop
open biop_zbs
open barrier_kind
open ast
open amoop
open agtype
open WaitReason
open TrapVectorMode
open Step
open SATPMode
open Register
open Privilege
open PmpAddrMatchType
open PTW_Error
open PTE_Check
open InterruptType
open ISA_Format
open HartState
open FetchResult
open Ext_PhysAddr_Check
open Ext_FetchAddr_Check
open Ext_DataAddr_Check
open Ext_ControlAddr_Check
open ExtStatus
open ExecutionResult
open ExceptionType
open Architecture
open AccessType

def mmu_type (_ : Unit) : SailM String := do
  assert (xlen == 64) "riscv_device_tree.sail:14.21-14.22"
  bif (hartSupports Ext_Sv57)
  then (pure "sv57")
  else
    (bif (hartSupports Ext_Sv48)
    then (pure "sv48")
    else
      (bif (hartSupports Ext_Sv39)
      then (pure "sv39")
      else (pure "none")))

def generate_isa_base (_ : Unit) : String :=
  (HAppend.hAppend "rv" (HAppend.hAppend (Int.repr xlen) "i"))

def undefined_ISA_Format (_ : Unit) : SailM ISA_Format := do
  (internal_pick [Canonical_Lowercase, DeviceTree_ISA_Extensions])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def ISA_Format_of_num (arg_ : Nat) : ISA_Format :=
  match arg_ with
  | 0 => Canonical_Lowercase
  | _ => DeviceTree_ISA_Extensions

def num_of_ISA_Format (arg_ : ISA_Format) : Int :=
  match arg_ with
  | Canonical_Lowercase => 0
  | DeviceTree_ISA_Extensions => 1

def ext_wrap (ext : extension) (fmt : ISA_Format) : String :=
  bif (not (hartSupports ext))
  then ""
  else
    (let s := (extensionName_forwards ext)
    match fmt with
    | Canonical_Lowercase =>
      (bif ((String.length s) == 1)
      then s
      else (HAppend.hAppend "_" s))
    | DeviceTree_ISA_Extensions => (HAppend.hAppend ", \"" (HAppend.hAppend s "\"")))

def generate_isa_string (fmt : ISA_Format) : String :=
  let prefix : String :=
    match fmt with
    | Canonical_Lowercase => (HAppend.hAppend "rv" (HAppend.hAppend (Int.repr xlen) "i"))
    | DeviceTree_ISA_Extensions => "\"i\""
  let singles :=
    (HAppend.hAppend ""
      (HAppend.hAppend (ext_wrap Ext_M fmt)
        (HAppend.hAppend (ext_wrap Ext_A fmt)
          (HAppend.hAppend (ext_wrap Ext_F fmt)
            (HAppend.hAppend (ext_wrap Ext_D fmt)
              (HAppend.hAppend (ext_wrap Ext_C fmt)
                (HAppend.hAppend (ext_wrap Ext_B fmt)
                  (HAppend.hAppend (ext_wrap Ext_V fmt) (ext_wrap Ext_H fmt)))))))))
  let zi_exts :=
    (HAppend.hAppend ""
      (HAppend.hAppend (ext_wrap Ext_Zicbom fmt)
        (HAppend.hAppend (ext_wrap Ext_Zicboz fmt)
          (HAppend.hAppend (ext_wrap Ext_Zicntr fmt)
            (HAppend.hAppend (ext_wrap Ext_Zicond fmt)
              (HAppend.hAppend (ext_wrap Ext_Zicsr fmt)
                (HAppend.hAppend (ext_wrap Ext_Zifencei fmt)
                  (HAppend.hAppend (ext_wrap Ext_Zihpm fmt)
                    (HAppend.hAppend (ext_wrap Ext_Zimop fmt) (ext_wrap Ext_Zmmul fmt))))))))))
  let za_exts :=
    (HAppend.hAppend ""
      (HAppend.hAppend (ext_wrap Ext_Zaamo fmt)
        (HAppend.hAppend (ext_wrap Ext_Zabha fmt)
          (HAppend.hAppend (ext_wrap Ext_Zalrsc fmt) (ext_wrap Ext_Zawrs fmt)))))
  let zf_exts :=
    (HAppend.hAppend ""
      (HAppend.hAppend (ext_wrap Ext_Zfa fmt)
        (HAppend.hAppend (ext_wrap Ext_Zfh fmt)
          (HAppend.hAppend (ext_wrap Ext_Zfhmin fmt)
            (HAppend.hAppend (ext_wrap Ext_Zfinx fmt)
              (HAppend.hAppend (ext_wrap Ext_Zdinx fmt)
                (HAppend.hAppend (ext_wrap Ext_Zhinx fmt) (ext_wrap Ext_Zhinxmin fmt))))))))
  let zc_exts :=
    (HAppend.hAppend ""
      (HAppend.hAppend (ext_wrap Ext_Zca fmt)
        (HAppend.hAppend (ext_wrap Ext_Zcb fmt)
          (HAppend.hAppend (ext_wrap Ext_Zcd fmt)
            (HAppend.hAppend (ext_wrap Ext_Zcf fmt) (ext_wrap Ext_Zcmop fmt))))))
  let zb_exts :=
    (HAppend.hAppend ""
      (HAppend.hAppend (ext_wrap Ext_Zba fmt)
        (HAppend.hAppend (ext_wrap Ext_Zbb fmt)
          (HAppend.hAppend (ext_wrap Ext_Zbc fmt)
            (HAppend.hAppend (ext_wrap Ext_Zbkb fmt)
              (HAppend.hAppend (ext_wrap Ext_Zbkc fmt)
                (HAppend.hAppend (ext_wrap Ext_Zbkx fmt) (ext_wrap Ext_Zbs fmt))))))))
  let zk_exts :=
    (HAppend.hAppend ""
      (HAppend.hAppend (ext_wrap Ext_Zknd fmt)
        (HAppend.hAppend (ext_wrap Ext_Zkne fmt)
          (HAppend.hAppend (ext_wrap Ext_Zknh fmt)
            (HAppend.hAppend (ext_wrap Ext_Zkr fmt)
              (HAppend.hAppend (ext_wrap Ext_Zksed fmt)
                (HAppend.hAppend (ext_wrap Ext_Zksh fmt) (ext_wrap Ext_Zkt fmt))))))))
  let zv_exts :=
    (HAppend.hAppend ""
      (HAppend.hAppend (ext_wrap Ext_Zvbb fmt)
        (HAppend.hAppend (ext_wrap Ext_Zvbc fmt)
          (HAppend.hAppend (ext_wrap Ext_Zvkb fmt)
            (HAppend.hAppend (ext_wrap Ext_Zvkg fmt)
              (HAppend.hAppend (ext_wrap Ext_Zvkned fmt)
                (HAppend.hAppend (ext_wrap Ext_Zvknha fmt)
                  (HAppend.hAppend (ext_wrap Ext_Zvknhb fmt)
                    (HAppend.hAppend (ext_wrap Ext_Zvksh fmt) (ext_wrap Ext_Zvkt fmt))))))))))
  let s_exts :=
    (HAppend.hAppend ""
      (HAppend.hAppend (ext_wrap Ext_Sscofpmf fmt)
        (HAppend.hAppend (ext_wrap Ext_Sstc fmt)
          (HAppend.hAppend (ext_wrap Ext_Svinval fmt)
            (HAppend.hAppend (ext_wrap Ext_Svnapot fmt) (ext_wrap Ext_Svpbmt fmt))))))
  let m_exts := (HAppend.hAppend "" (ext_wrap Ext_Smcntrpmf fmt))
  (HAppend.hAppend prefix
    (HAppend.hAppend singles
      (HAppend.hAppend zi_exts
        (HAppend.hAppend za_exts
          (HAppend.hAppend zf_exts
            (HAppend.hAppend zc_exts
              (HAppend.hAppend zb_exts
                (HAppend.hAppend zk_exts (HAppend.hAppend zv_exts (HAppend.hAppend s_exts m_exts))))))))))

def generate_dts (_ : Unit) : SailM String := do
  let clock_freq : Int := 1000000000
  let ram_base_hi ← do (pure (BitVec.toNat (shiftr (← readReg plat_ram_base) 32)))
  let ram_base_lo ← do
    (pure (BitVec.toNat (Sail.BitVec.extractLsb (← readReg plat_ram_base) 31 0)))
  let ram_size_hi ← do (pure (BitVec.toNat (shiftr (← readReg plat_ram_size) 32)))
  let ram_size_lo ← do
    (pure (BitVec.toNat (Sail.BitVec.extractLsb (← readReg plat_ram_size) 31 0)))
  let clint_base_hi ← do (pure (BitVec.toNat (shiftr (← readReg plat_clint_base) 32)))
  let clint_base_lo ← do
    (pure (BitVec.toNat (Sail.BitVec.extractLsb (← readReg plat_clint_base) 31 0)))
  let clint_size_hi ← do (pure (BitVec.toNat (shiftr (← readReg plat_clint_size) 32)))
  let clint_size_lo ← do
    (pure (BitVec.toNat (Sail.BitVec.extractLsb (← readReg plat_clint_size) 31 0)))
  (pure (HAppend.hAppend "/dts-v1/;
"
      (HAppend.hAppend "
"
        (HAppend.hAppend "/ {
"
          (HAppend.hAppend "  #address-cells = <2>;
"
            (HAppend.hAppend "  #size-cells = <2>;
"
              (HAppend.hAppend "  compatible = \"ucbbar,spike-bare-dev\";
"
                (HAppend.hAppend "  model = \"ucbbar,spike-bare\";
"
                  (HAppend.hAppend "  cpus {
"
                    (HAppend.hAppend "    #address-cells = <1>;
"
                      (HAppend.hAppend "    #size-cells = <0>;
"
                        (HAppend.hAppend "    timebase-frequency = <"
                          (HAppend.hAppend (Int.repr (Int.tdiv clock_freq plat_insns_per_tick))
                            (HAppend.hAppend ">;
"
                              (HAppend.hAppend "    CPU0: cpu@0 {
"
                                (HAppend.hAppend "      device_type = \"cpu\";
"
                                  (HAppend.hAppend "      reg = <0>;
"
                                    (HAppend.hAppend "      status = \"okay\";
"
                                      (HAppend.hAppend "      compatible = \"riscv\";
"
                                        (HAppend.hAppend "      riscv,isa-base = \""
                                          (HAppend.hAppend (generate_isa_base ())
                                            (HAppend.hAppend "\";
"
                                              (HAppend.hAppend "      riscv,isa = \""
                                                (HAppend.hAppend
                                                  (generate_isa_string Canonical_Lowercase)
                                                  (HAppend.hAppend "\";
"
                                                    (HAppend.hAppend "      riscv,isa-extensions = "
                                                      (HAppend.hAppend
                                                        (generate_isa_string
                                                          DeviceTree_ISA_Extensions)
                                                        (HAppend.hAppend ";
"
                                                          (HAppend.hAppend
                                                            "      mmu-type = \"riscv,"
                                                            (HAppend.hAppend (← (mmu_type ()))
                                                              (HAppend.hAppend "\";
"
                                                                (HAppend.hAppend
                                                                  "      clock-frequency = <"
                                                                  (HAppend.hAppend
                                                                    (Int.repr clock_freq)
                                                                    (HAppend.hAppend ">;
"
                                                                      (HAppend.hAppend
                                                                        "      CPU0_intc: interrupt-controller {
"
                                                                        (HAppend.hAppend
                                                                          "        #address-cells = <2>;
"
                                                                          (HAppend.hAppend
                                                                            "        #interrupt-cells = <1>;
"
                                                                            (HAppend.hAppend
                                                                              "        interrupt-controller;
"
                                                                              (HAppend.hAppend
                                                                                "        compatible = \"riscv,cpu-intc\";
"
                                                                                (HAppend.hAppend
                                                                                  "      };
"
                                                                                  (HAppend.hAppend
                                                                                    "    };
"
                                                                                    (HAppend.hAppend
                                                                                      "  };
"
                                                                                      (HAppend.hAppend
                                                                                        "  memory@"
                                                                                        (HAppend.hAppend
                                                                                          (String.drop
                                                                                            (Int.toHex
                                                                                              (BitVec.toNat
                                                                                                (← readReg plat_ram_base)))
                                                                                            2)
                                                                                          (HAppend.hAppend
                                                                                            " {
"
                                                                                            (HAppend.hAppend
                                                                                              "    device_type = \"memory\";
"
                                                                                              (HAppend.hAppend
                                                                                                "    reg = <"
                                                                                                (HAppend.hAppend
                                                                                                  (Int.toHex
                                                                                                    ram_base_hi)
                                                                                                  (HAppend.hAppend
                                                                                                    " "
                                                                                                    (HAppend.hAppend
                                                                                                      (Int.toHex
                                                                                                        ram_base_lo)
                                                                                                      (HAppend.hAppend
                                                                                                        " "
                                                                                                        (HAppend.hAppend
                                                                                                          (Int.toHex
                                                                                                            ram_size_hi)
                                                                                                          (HAppend.hAppend
                                                                                                            " "
                                                                                                            (HAppend.hAppend
                                                                                                              (Int.toHex
                                                                                                                ram_size_lo)
                                                                                                              (HAppend.hAppend
                                                                                                                ">;
"
                                                                                                                (HAppend.hAppend
                                                                                                                  "  };
"
                                                                                                                  (HAppend.hAppend
                                                                                                                    "  soc {
"
                                                                                                                    (HAppend.hAppend
                                                                                                                      "    #address-cells = <2>;
"
                                                                                                                      (HAppend.hAppend
                                                                                                                        "    #size-cells = <2>;
"
                                                                                                                        (HAppend.hAppend
                                                                                                                          "    compatible = \"ucbbar,spike-bare-soc\", \"simple-bus\";
"
                                                                                                                          (HAppend.hAppend
                                                                                                                            "    ranges;
"
                                                                                                                            (HAppend.hAppend
                                                                                                                              "    clint@"
                                                                                                                              (HAppend.hAppend
                                                                                                                                (String.drop
                                                                                                                                  (Int.toHex
                                                                                                                                    (BitVec.toNat
                                                                                                                                      (← readReg plat_clint_base)))
                                                                                                                                  2)
                                                                                                                                (HAppend.hAppend
                                                                                                                                  " {
"
                                                                                                                                  (HAppend.hAppend
                                                                                                                                    "      compatible = \"riscv,clint0\";
"
                                                                                                                                    (HAppend.hAppend
                                                                                                                                      "      interrupts-extended = <&CPU0_intc 3 &CPU0_intc 7>;
"
                                                                                                                                      (HAppend.hAppend
                                                                                                                                        "      reg = <"
                                                                                                                                        (HAppend.hAppend
                                                                                                                                          (Int.toHex
                                                                                                                                            clint_base_hi)
                                                                                                                                          (HAppend.hAppend
                                                                                                                                            " "
                                                                                                                                            (HAppend.hAppend
                                                                                                                                              (Int.toHex
                                                                                                                                                clint_base_lo)
                                                                                                                                              (HAppend.hAppend
                                                                                                                                                " "
                                                                                                                                                (HAppend.hAppend
                                                                                                                                                  (Int.toHex
                                                                                                                                                    clint_size_hi)
                                                                                                                                                  (HAppend.hAppend
                                                                                                                                                    " "
                                                                                                                                                    (HAppend.hAppend
                                                                                                                                                      (Int.toHex
                                                                                                                                                        clint_size_lo)
                                                                                                                                                      (HAppend.hAppend
                                                                                                                                                        ">;
"
                                                                                                                                                        (HAppend.hAppend
                                                                                                                                                          "    };
"
                                                                                                                                                          (HAppend.hAppend
                                                                                                                                                            "  };
"
                                                                                                                                                            (HAppend.hAppend
                                                                                                                                                              "  htif {
"
                                                                                                                                                              (HAppend.hAppend
                                                                                                                                                                "    compatible = \"ucb,htif0\";
"
                                                                                                                                                                (HAppend.hAppend
                                                                                                                                                                  "  };
"
                                                                                                                                                                  "};
"))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def generate_canonical_isa_string (_ : Unit) : String :=
  (generate_isa_string Canonical_Lowercase)

