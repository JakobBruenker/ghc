
-- | Hard wired things related to registers.
--      This is module is preventing the native code generator being able to
--      emit code for non-host architectures.
--
--      TODO: Do a better job of the overloading, and eliminate this module.
--      We'd probably do better with a Register type class, and hook this to
--      Instruction somehow.
--
--      TODO: We should also make arch specific versions of RegAlloc.Graph.TrivColorable
module GHC.CmmToAsm.Reg.Target (
        targetVirtualRegSqueeze,
        targetRealRegSqueeze,
        targetClassOfRealReg,
        targetMkVirtualReg,
        targetRegDotColor,
        targetClassOfReg
)

where

import GHC.Prelude

import GHC.Platform.Reg
import GHC.Platform.Reg.Class
import GHC.CmmToAsm.Format

import GHC.Utils.Outputable
import GHC.Utils.Panic
import GHC.Types.Unique
import GHC.Platform

import qualified GHC.CmmToAsm.X86.Regs       as X86
import qualified GHC.CmmToAsm.X86.RegInfo    as X86
import qualified GHC.CmmToAsm.PPC.Regs       as PPC
import qualified GHC.CmmToAsm.SPARC.Regs     as SPARC

targetVirtualRegSqueeze :: Platform -> RegClass -> VirtualReg -> Int
targetVirtualRegSqueeze platform
    = case platformArch platform of
      ArchX86       -> X86.virtualRegSqueeze
      ArchX86_64    -> X86.virtualRegSqueeze
      ArchPPC       -> PPC.virtualRegSqueeze
      ArchS390X     -> panic "targetVirtualRegSqueeze ArchS390X"
      ArchSPARC     -> SPARC.virtualRegSqueeze
      ArchSPARC64   -> panic "targetVirtualRegSqueeze ArchSPARC64"
      ArchPPC_64 _  -> PPC.virtualRegSqueeze
      ArchARM _ _ _ -> panic "targetVirtualRegSqueeze ArchARM"
      ArchAArch64   -> panic "targetVirtualRegSqueeze ArchAArch64"
      ArchAlpha     -> panic "targetVirtualRegSqueeze ArchAlpha"
      ArchMipseb    -> panic "targetVirtualRegSqueeze ArchMipseb"
      ArchMipsel    -> panic "targetVirtualRegSqueeze ArchMipsel"
      ArchRISCV64   -> panic "targetVirtualRegSqueeze ArchRISCV64"
      ArchJavaScript-> panic "targetVirtualRegSqueeze ArchJavaScript"
      ArchUnknown   -> panic "targetVirtualRegSqueeze ArchUnknown"


targetRealRegSqueeze :: Platform -> RegClass -> RealReg -> Int
targetRealRegSqueeze platform
    = case platformArch platform of
      ArchX86       -> X86.realRegSqueeze
      ArchX86_64    -> X86.realRegSqueeze
      ArchPPC       -> PPC.realRegSqueeze
      ArchS390X     -> panic "targetRealRegSqueeze ArchS390X"
      ArchSPARC     -> SPARC.realRegSqueeze
      ArchSPARC64   -> panic "targetRealRegSqueeze ArchSPARC64"
      ArchPPC_64 _  -> PPC.realRegSqueeze
      ArchARM _ _ _ -> panic "targetRealRegSqueeze ArchARM"
      ArchAArch64   -> panic "targetRealRegSqueeze ArchAArch64"
      ArchAlpha     -> panic "targetRealRegSqueeze ArchAlpha"
      ArchMipseb    -> panic "targetRealRegSqueeze ArchMipseb"
      ArchMipsel    -> panic "targetRealRegSqueeze ArchMipsel"
      ArchRISCV64   -> panic "targetRealRegSqueeze ArchRISCV64"
      ArchJavaScript-> panic "targetRealRegSqueeze ArchJavaScript"
      ArchUnknown   -> panic "targetRealRegSqueeze ArchUnknown"

targetClassOfRealReg :: Platform -> RealReg -> RegClass
targetClassOfRealReg platform
    = case platformArch platform of
      ArchX86       -> X86.classOfRealReg platform
      ArchX86_64    -> X86.classOfRealReg platform
      ArchPPC       -> PPC.classOfRealReg
      ArchS390X     -> panic "targetClassOfRealReg ArchS390X"
      ArchSPARC     -> SPARC.classOfRealReg
      ArchSPARC64   -> panic "targetClassOfRealReg ArchSPARC64"
      ArchPPC_64 _  -> PPC.classOfRealReg
      ArchARM _ _ _ -> panic "targetClassOfRealReg ArchARM"
      ArchAArch64   -> panic "targetClassOfRealReg ArchAArch64"
      ArchAlpha     -> panic "targetClassOfRealReg ArchAlpha"
      ArchMipseb    -> panic "targetClassOfRealReg ArchMipseb"
      ArchMipsel    -> panic "targetClassOfRealReg ArchMipsel"
      ArchRISCV64   -> panic "targetClassOfRealReg ArchRISCV64"
      ArchJavaScript-> panic "targetClassOfRealReg ArchJavaScript"
      ArchUnknown   -> panic "targetClassOfRealReg ArchUnknown"

targetMkVirtualReg :: Platform -> Unique -> Format -> VirtualReg
targetMkVirtualReg platform
    = case platformArch platform of
      ArchX86       -> X86.mkVirtualReg
      ArchX86_64    -> X86.mkVirtualReg
      ArchPPC       -> PPC.mkVirtualReg
      ArchS390X     -> panic "targetMkVirtualReg ArchS390X"
      ArchSPARC     -> SPARC.mkVirtualReg
      ArchSPARC64   -> panic "targetMkVirtualReg ArchSPARC64"
      ArchPPC_64 _  -> PPC.mkVirtualReg
      ArchARM _ _ _ -> panic "targetMkVirtualReg ArchARM"
      ArchAArch64   -> panic "targetMkVirtualReg ArchAArch64"
      ArchAlpha     -> panic "targetMkVirtualReg ArchAlpha"
      ArchMipseb    -> panic "targetMkVirtualReg ArchMipseb"
      ArchMipsel    -> panic "targetMkVirtualReg ArchMipsel"
      ArchRISCV64   -> panic "targetMkVirtualReg ArchRISCV64"
      ArchJavaScript-> panic "targetMkVirtualReg ArchJavaScript"
      ArchUnknown   -> panic "targetMkVirtualReg ArchUnknown"

targetRegDotColor :: Platform -> RealReg -> SDoc
targetRegDotColor platform
    = case platformArch platform of
      ArchX86       -> X86.regDotColor platform
      ArchX86_64    -> X86.regDotColor platform
      ArchPPC       -> PPC.regDotColor
      ArchS390X     -> panic "targetRegDotColor ArchS390X"
      ArchSPARC     -> SPARC.regDotColor
      ArchSPARC64   -> panic "targetRegDotColor ArchSPARC64"
      ArchPPC_64 _  -> PPC.regDotColor
      ArchARM _ _ _ -> panic "targetRegDotColor ArchARM"
      ArchAArch64   -> panic "targetRegDotColor ArchAArch64"
      ArchAlpha     -> panic "targetRegDotColor ArchAlpha"
      ArchMipseb    -> panic "targetRegDotColor ArchMipseb"
      ArchMipsel    -> panic "targetRegDotColor ArchMipsel"
      ArchRISCV64   -> panic "targetRegDotColor ArchRISCV64"
      ArchJavaScript-> panic "targetRegDotColor ArchJavaScript"
      ArchUnknown   -> panic "targetRegDotColor ArchUnknown"


targetClassOfReg :: Platform -> Reg -> RegClass
targetClassOfReg platform reg
 = case reg of
   RegVirtual vr -> classOfVirtualReg vr
   RegReal rr -> targetClassOfRealReg platform rr
