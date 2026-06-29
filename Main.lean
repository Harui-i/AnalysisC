import Std.Data.HashMap
import VersoManual

import AnalysisC.ReportPage

open Verso Doc
open Verso.Genre Manual

open Std (HashMap)

open AnalysisC

def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2

def main := manualMain (%doc AnalysisC.ReportPage) (config := config)
