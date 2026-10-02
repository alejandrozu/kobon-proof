import Kobon.HybridBoundary
import Kobon.BBLExtrema
import Kobon.TamuraTangentBounds
import Mathlib.Tactic.FinCases

/-! A complete real-parameter 33-line seed certificate.
The rational slopes are fixed. The intercepts are actual tan(k*pi/32).
The finite box checks use native_decide; geometry and trigonometric bounds are
proved by the generic soundness theorems. This does not formalize BBL doubling.
-/
namespace Kobon.TamuraSeed33
open Parametric Exterior HybridBoundary BBLExtrema Real
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def lo : Form 16 := ![(98491403357164253077197521291327432293/1000000000000000000000000000000000000000),(994561836898290034557988113223381142989/5000000000000000000000000000000000000000),(3033466836073423916758839469412998723841/10000000000000000000000000000000000000000),(129441738241592202750527726315530649553/312500000000000000000000000000000000000),(267255567975395820544842980647681454291/500000000000000000000000000000000000000),(1670446594798247299994394216307701903881/2500000000000000000000000000000000000000),(8206787908286603309722819853310115987673/10000000000000000000000000000000000000000),1,(1218503525587976344795477230620364055963/1000000000000000000000000000000000000000),(7483028813327445088005675674712384593459/5000000000000000000000000000000000000000),(18708684117893894810852013343415244316869/10000000000000000000000000000000000000000),(754441738241592202750527726315530649553/312500000000000000000000000000000000000),(16482791044691602134390771084131268548839/5000000000000000000000000000000000000000),(50273394921258481045149750710640723857371/10000000000000000000000000000000000000000),(50765851938044302310535738317097361018837/5000000000000000000000000000000000000000),0]
def hi : Form 16 := ![(984914033571642530771975212913274322931/10000000000000000000000000000000000000000),(1989123673796580069115976226446762285979/10000000000000000000000000000000000000000),(1516733418036711958379419734706499361921/5000000000000000000000000000000000000000),(4142135623730950488016887242096980785697/10000000000000000000000000000000000000000),(5345111359507916410896859612953629085821/10000000000000000000000000000000000000000),(267271455167719567999103074609232304621/400000000000000000000000000000000000000),(4103393954143301654861409926655057993837/5000000000000000000000000000000000000000),1,(12185035255879763447954772306203640559631/10000000000000000000000000000000000000000),(14966057626654890176011351349424769186919/10000000000000000000000000000000000000000),(1870868411789389481085201334341524431687/1000000000000000000000000000000000000000),(24142135623730950488016887242096980785697/10000000000000000000000000000000000000000),(32965582089383204268781542168262537097679/10000000000000000000000000000000000000000),(12568348730314620261287437677660180964343/2500000000000000000000000000000000000000),(4061268155043544184842859065367788881507/400000000000000000000000000000000000000),(1/100000)]

def lines : Array (ParamLine 16) := #[
  ⟨0,-1,![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩,
  ⟨(-66666666666666666666666666666666666666666667/1000000000000000000000000000000000000000000000),-1,![0,0,0,0,0,0,0,(66666666666666666666666666666666666666666667/1000000000000000000000000000000000000000000000),0,0,0,0,0,0,0,0]⟩,
  ⟨(1/10),-1,![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,(-1/10)]⟩,
  ⟨(-1/10),-1,![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,(-1/10)]⟩,
  ⟨(33333333333333333333333333333333333333333333/1000000000000000000000000000000000000000000000),-1,![0,0,0,0,0,0,0,(33333333333333333333333333333333333333333333/1000000000000000000000000000000000000000000000),0,0,0,0,0,0,0,0]⟩,
  ⟨(-22481533926154733286197764456781802101/1000000000000000000000000000000000000000000000),-1,![0,0,0,0,0,0,0,0,0,0,0,(22481533926154733286197764456781802101/1000000000000000000000000000000000000000000000),0,0,0,0]⟩,
  ⟨(-703032999033280976920568160107764649/31250000000000000000000000000000000000000000),-1,![0,0,0,(703032999033280976920568160107764649/31250000000000000000000000000000000000000000),0,0,0,0,0,0,0,0,0,0,0,0]⟩,
  ⟨(703032999033280976920568160107764649/31250000000000000000000000000000000000000000),-1,![0,0,0,(703032999033280976920568160107764649/31250000000000000000000000000000000000000000),0,0,0,0,0,0,0,0,0,0,0,0]⟩,
  ⟨(22481533926154733286197764456781802101/1000000000000000000000000000000000000000000000),-1,![0,0,0,0,0,0,0,0,0,0,0,(22481533926154733286197764456781802101/1000000000000000000000000000000000000000000000),0,0,0,0]⟩,
  ⟨(-400623661767070365368893791/50000000000000000000000000000000000000000000),-1,![0,0,0,0,0,0,0,0,0,0,0,0,0,(400623661767070365368893791/50000000000000000000000000000000000000000000),0,0]⟩,
  ⟨(-4835959141374757692845806123/250000000000000000000000000000000000000000000),-1,![0,0,0,0,0,0,0,0,0,(4835959141374757692845806123/250000000000000000000000000000000000000000000),0,0,0,0,0,0]⟩,
  ⟨(-19343902732348844470002204743/1000000000000000000000000000000000000000000000),-1,![0,0,0,0,0,(19343902732348844470002204743/1000000000000000000000000000000000000000000000),0,0,0,0,0,0,0,0,0,0]⟩,
  ⟨(-2003214721000905118950905561/250000000000000000000000000000000000000000000),-1,![0,(2003214721000905118950905561/250000000000000000000000000000000000000000000),0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩,
  ⟨(2003214721000905118950905561/250000000000000000000000000000000000000000000),-1,![0,(2003214721000905118950905561/250000000000000000000000000000000000000000000),0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩,
  ⟨(19343902732348844470002204743/1000000000000000000000000000000000000000000000),-1,![0,0,0,0,0,(19343902732348844470002204743/1000000000000000000000000000000000000000000000),0,0,0,0,0,0,0,0,0,0]⟩,
  ⟨(4835959141374757692845806123/250000000000000000000000000000000000000000000),-1,![0,0,0,0,0,0,0,0,0,(4835959141374757692845806123/250000000000000000000000000000000000000000000),0,0,0,0,0,0]⟩,
  ⟨(400623661767070365368893791/50000000000000000000000000000000000000000000),-1,![0,0,0,0,0,0,0,0,0,0,0,0,0,(400623661767070365368893791/50000000000000000000000000000000000000000000),0,0]⟩,
  ⟨(-710841063967541/500000000000000000000000000000000000000000000),-1,![0,0,0,0,0,0,0,0,0,0,0,0,0,0,(710841063967541/500000000000000000000000000000000000000000000),0]⟩,
  ⟨(-404860817734011/100000000000000000000000000000000000000000000),-1,![0,0,0,0,0,0,0,0,0,0,0,0,(404860817734011/100000000000000000000000000000000000000000000),0,0,0]⟩,
  ⟨(-6059170363956583/1000000000000000000000000000000000000000000000),-1,![0,0,0,0,0,0,0,0,0,0,(6059170363956583/1000000000000000000000000000000000000000000000),0,0,0,0,0]⟩,
  ⟨(-1786819712103349/250000000000000000000000000000000000000000000),-1,![0,0,0,0,0,0,0,0,(1786819712103349/250000000000000000000000000000000000000000000),0,0,0,0,0,0,0]⟩,
  ⟨(-1786819755302843/250000000000000000000000000000000000000000000),-1,![0,0,0,0,0,0,(1786819755302843/250000000000000000000000000000000000000000000),0,0,0,0,0,0,0,0,0]⟩,
  ⟨(-6059170944412779/1000000000000000000000000000000000000000000000),-1,![0,0,0,0,(6059170944412779/1000000000000000000000000000000000000000000000),0,0,0,0,0,0,0,0,0,0,0]⟩,
  ⟨(-2024304738731311/500000000000000000000000000000000000000000000),-1,![0,0,(2024304738731311/500000000000000000000000000000000000000000000),0,0,0,0,0,0,0,0,0,0,0,0,0]⟩,
  ⟨(-1421686495255729/1000000000000000000000000000000000000000000000),-1,![(1421686495255729/1000000000000000000000000000000000000000000000),0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩,
  ⟨(1421686495255729/1000000000000000000000000000000000000000000000),-1,![(1421686495255729/1000000000000000000000000000000000000000000000),0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]⟩,
  ⟨(2024304738731311/500000000000000000000000000000000000000000000),-1,![0,0,(2024304738731311/500000000000000000000000000000000000000000000),0,0,0,0,0,0,0,0,0,0,0,0,0]⟩,
  ⟨(6059170944412779/1000000000000000000000000000000000000000000000),-1,![0,0,0,0,(6059170944412779/1000000000000000000000000000000000000000000000),0,0,0,0,0,0,0,0,0,0,0]⟩,
  ⟨(1786819755302843/250000000000000000000000000000000000000000000),-1,![0,0,0,0,0,0,(1786819755302843/250000000000000000000000000000000000000000000),0,0,0,0,0,0,0,0,0]⟩,
  ⟨(1786819712103349/250000000000000000000000000000000000000000000),-1,![0,0,0,0,0,0,0,0,(1786819712103349/250000000000000000000000000000000000000000000),0,0,0,0,0,0,0]⟩,
  ⟨(6059170363956583/1000000000000000000000000000000000000000000000),-1,![0,0,0,0,0,0,0,0,0,0,(6059170363956583/1000000000000000000000000000000000000000000000),0,0,0,0,0]⟩,
  ⟨(404860817734011/100000000000000000000000000000000000000000000),-1,![0,0,0,0,0,0,0,0,0,0,0,0,(404860817734011/100000000000000000000000000000000000000000000),0,0,0]⟩,
  ⟨(710841063967541/500000000000000000000000000000000000000000000),-1,![0,0,0,0,0,0,0,0,0,0,0,0,0,0,(710841063967541/500000000000000000000000000000000000000000000),0]⟩]

def lineAt (i : Nat) : ParamLine 16 := lines[i]!

def triangles : List Triple := [⟨0,1,20⟩,⟨0,1,21⟩,⟨0,2,3⟩,⟨0,2,24⟩,⟨0,3,25⟩,⟨0,4,28⟩,⟨0,4,29⟩,⟨0,5,18⟩,⟨0,5,19⟩,⟨0,6,22⟩,⟨0,6,23⟩,⟨0,7,26⟩,⟨0,7,27⟩,⟨0,8,30⟩,⟨0,8,31⟩,⟨0,9,17⟩,⟨0,9,18⟩,⟨0,10,19⟩,⟨0,10,20⟩,⟨0,11,21⟩,⟨0,11,22⟩,⟨0,12,23⟩,⟨0,12,24⟩,⟨0,13,25⟩,⟨0,13,26⟩,⟨0,14,27⟩,⟨0,14,28⟩,⟨0,15,29⟩,⟨0,15,30⟩,⟨0,16,31⟩,⟨0,16,32⟩,⟨1,2,4⟩,⟨1,2,8⟩,⟨1,3,4⟩,⟨1,5,7⟩,⟨1,5,15⟩,⟨1,6,12⟩,⟨1,7,8⟩,⟨1,9,13⟩,⟨1,9,14⟩,⟨1,10,13⟩,⟨1,10,30⟩,⟨1,11,12⟩,⟨1,11,23⟩,⟨1,14,16⟩,⟨1,15,16⟩,⟨1,17,27⟩,⟨1,17,28⟩,⟨1,18,26⟩,⟨1,18,27⟩,⟨1,19,25⟩,⟨1,19,26⟩,⟨1,20,25⟩,⟨1,21,24⟩,⟨1,22,23⟩,⟨1,22,24⟩,⟨1,28,32⟩,⟨1,29,31⟩,⟨1,29,32⟩,⟨1,30,31⟩,⟨2,5,7⟩,⟨2,5,8⟩,⟨2,6,7⟩,⟨2,6,16⟩,⟨2,9,15⟩,⟨2,9,16⟩,⟨2,10,14⟩,⟨2,10,15⟩,⟨2,11,13⟩,⟨2,11,14⟩,⟨2,12,13⟩,⟨2,12,32⟩,⟨2,17,31⟩,⟨2,17,32⟩,⟨2,18,30⟩,⟨2,18,31⟩,⟨2,19,29⟩,⟨2,19,30⟩,⟨2,20,28⟩,⟨2,20,29⟩,⟨2,21,27⟩,⟨2,21,28⟩,⟨2,22,26⟩,⟨2,22,27⟩,⟨2,23,25⟩,⟨2,23,26⟩,⟨2,24,25⟩,⟨3,4,5⟩,⟨3,5,8⟩,⟨3,6,7⟩,⟨3,6,8⟩,⟨3,7,9⟩,⟨3,9,16⟩,⟨3,10,15⟩,⟨3,10,16⟩,⟨3,11,14⟩,⟨3,11,15⟩,⟨3,12,13⟩,⟨3,12,14⟩,⟨3,13,17⟩,⟨3,17,32⟩,⟨3,18,31⟩,⟨3,18,32⟩,⟨3,19,30⟩,⟨3,19,31⟩,⟨3,20,29⟩,⟨3,20,30⟩,⟨3,21,28⟩,⟨3,21,29⟩,⟨3,22,27⟩,⟨3,22,28⟩,⟨3,23,26⟩,⟨3,23,27⟩,⟨3,24,25⟩,⟨3,24,26⟩,⟨4,5,6⟩,⟨4,6,8⟩,⟨4,7,13⟩,⟨4,8,10⟩,⟨4,9,10⟩,⟨4,9,11⟩,⟨4,11,16⟩,⟨4,12,15⟩,⟨4,12,16⟩,⟨4,13,14⟩,⟨4,14,26⟩,⟨4,15,19⟩,⟨4,17,20⟩,⟨4,17,21⟩,⟨4,18,19⟩,⟨4,18,20⟩,⟨4,21,32⟩,⟨4,22,31⟩,⟨4,22,32⟩,⟨4,23,30⟩,⟨4,23,31⟩,⟨4,24,29⟩,⟨4,24,30⟩,⟨4,25,27⟩,⟨4,25,28⟩,⟨4,26,27⟩,⟨5,9,13⟩,⟨5,9,29⟩,⟨5,10,12⟩,⟨5,10,22⟩,⟨5,11,12⟩,⟨5,13,16⟩,⟨5,14,15⟩,⟨5,14,16⟩,⟨5,17,25⟩,⟨5,17,26⟩,⟨5,18,25⟩,⟨5,19,24⟩,⟨5,20,23⟩,⟨5,20,24⟩,⟨5,21,22⟩,⟨5,21,23⟩,⟨5,26,32⟩,⟨5,27,31⟩,⟨5,27,32⟩,⟨5,28,30⟩,⟨5,28,31⟩,⟨5,29,30⟩,⟨6,9,14⟩,⟨6,9,15⟩,⟨6,10,13⟩,⟨6,10,14⟩,⟨6,11,13⟩,⟨6,11,31⟩,⟨6,12,24⟩,⟨6,15,16⟩,⟨6,17,29⟩,⟨6,17,30⟩,⟨6,18,28⟩,⟨6,18,29⟩,⟨6,19,27⟩,⟨6,19,28⟩,⟨6,20,26⟩,⟨6,20,27⟩,⟨6,21,25⟩,⟨6,21,26⟩,⟨6,22,25⟩,⟨6,23,24⟩,⟨6,30,32⟩,⟨6,31,32⟩,⟨7,9,10⟩,⟨7,10,16⟩,⟨7,11,15⟩,⟨7,11,16⟩,⟨7,12,14⟩,⟨7,12,15⟩,⟨7,13,25⟩,⟨7,14,18⟩,⟨7,17,18⟩,⟨7,17,19⟩,⟨7,19,32⟩,⟨7,20,31⟩,⟨7,20,32⟩,⟨7,21,30⟩,⟨7,21,31⟩,⟨7,22,29⟩,⟨7,22,30⟩,⟨7,23,28⟩,⟨7,23,29⟩,⟨7,24,27⟩,⟨7,24,28⟩,⟨7,25,26⟩,⟨8,9,11⟩,⟨8,9,12⟩,⟨8,10,11⟩,⟨8,12,16⟩,⟨8,13,14⟩,⟨8,13,15⟩,⟨8,15,27⟩,⟨8,16,20⟩,⟨8,17,22⟩,⟨8,17,23⟩,⟨8,18,21⟩,⟨8,18,22⟩,⟨8,19,20⟩,⟨8,19,21⟩,⟨8,23,32⟩,⟨8,24,31⟩,⟨8,24,32⟩,⟨8,25,29⟩,⟨8,25,30⟩,⟨8,26,28⟩,⟨8,26,29⟩,⟨8,27,28⟩,⟨9,17,25⟩,⟨9,18,24⟩,⟨9,19,23⟩,⟨9,19,24⟩,⟨9,20,22⟩,⟨9,20,23⟩,⟨9,21,22⟩,⟨9,25,32⟩,⟨9,26,31⟩,⟨9,26,32⟩,⟨9,27,30⟩,⟨9,27,31⟩,⟨9,28,29⟩,⟨9,28,30⟩,⟨10,17,26⟩,⟨10,17,27⟩,⟨10,18,25⟩,⟨10,18,26⟩,⟨10,19,25⟩,⟨10,20,24⟩,⟨10,21,23⟩,⟨10,21,24⟩,⟨10,22,23⟩,⟨10,27,32⟩,⟨10,28,31⟩,⟨10,28,32⟩,⟨10,29,30⟩,⟨10,29,31⟩,⟨11,17,28⟩,⟨11,17,29⟩,⟨11,18,27⟩,⟨11,18,28⟩,⟨11,19,26⟩,⟨11,19,27⟩,⟨11,20,25⟩,⟨11,20,26⟩,⟨11,21,25⟩,⟨11,22,24⟩,⟨11,23,24⟩,⟨11,29,32⟩,⟨11,30,31⟩,⟨11,30,32⟩,⟨12,17,30⟩,⟨12,17,31⟩,⟨12,18,29⟩,⟨12,18,30⟩,⟨12,19,28⟩,⟨12,19,29⟩,⟨12,20,27⟩,⟨12,20,28⟩,⟨12,21,26⟩,⟨12,21,27⟩,⟨12,22,25⟩,⟨12,22,26⟩,⟨12,23,25⟩,⟨12,31,32⟩,⟨13,17,18⟩,⟨13,18,32⟩,⟨13,19,31⟩,⟨13,19,32⟩,⟨13,20,30⟩,⟨13,20,31⟩,⟨13,21,29⟩,⟨13,21,30⟩,⟨13,22,28⟩,⟨13,22,29⟩,⟨13,23,27⟩,⟨13,23,28⟩,⟨13,24,26⟩,⟨13,24,27⟩,⟨14,17,19⟩,⟨14,17,20⟩,⟨14,18,19⟩,⟨14,20,32⟩,⟨14,21,31⟩,⟨14,21,32⟩,⟨14,22,30⟩,⟨14,22,31⟩,⟨14,23,29⟩,⟨14,23,30⟩,⟨14,24,28⟩,⟨14,24,29⟩,⟨14,25,26⟩,⟨14,25,27⟩,⟨15,17,21⟩,⟨15,17,22⟩,⟨15,18,20⟩,⟨15,18,21⟩,⟨15,19,20⟩,⟨15,22,32⟩,⟨15,23,31⟩,⟨15,23,32⟩,⟨15,24,30⟩,⟨15,24,31⟩,⟨15,25,28⟩,⟨15,25,29⟩,⟨15,26,27⟩,⟨15,26,28⟩,⟨16,17,23⟩,⟨16,17,24⟩,⟨16,18,22⟩,⟨16,18,23⟩,⟨16,19,21⟩,⟨16,19,22⟩,⟨16,20,21⟩,⟨16,24,32⟩,⟨16,25,30⟩,⟨16,25,31⟩,⟨16,26,29⟩,⟨16,26,30⟩,⟨16,27,28⟩,⟨16,27,29⟩]

def distinguished : List Triple := [⟨0,1,20⟩,⟨0,1,21⟩,⟨0,2,3⟩,⟨0,2,24⟩,⟨0,3,25⟩,⟨0,4,28⟩,⟨0,4,29⟩,⟨0,5,18⟩,⟨0,5,19⟩,⟨0,6,22⟩,⟨0,6,23⟩,⟨0,7,26⟩,⟨0,7,27⟩,⟨0,8,30⟩,⟨0,8,31⟩,⟨0,9,17⟩,⟨0,9,18⟩,⟨0,10,19⟩,⟨0,10,20⟩,⟨0,11,21⟩,⟨0,11,22⟩,⟨0,12,23⟩,⟨0,12,24⟩,⟨0,13,25⟩,⟨0,13,26⟩,⟨0,14,27⟩,⟨0,14,28⟩,⟨0,15,29⟩,⟨0,15,30⟩,⟨0,16,31⟩,⟨0,16,32⟩]

def visible : List Triple := [⟨0,32,33⟩,⟨1,3,33⟩,⟨4,7,33⟩,⟨5,6,33⟩,⟨8,14,33⟩,⟨9,12,33⟩,⟨10,11,33⟩,⟨13,15,33⟩,⟨16,28,33⟩,⟨17,24,33⟩,⟨18,23,33⟩,⟨19,22,33⟩,⟨20,21,33⟩,⟨25,31,33⟩,⟨26,30,33⟩,⟨27,29,33⟩]

def rightSlope : ℚ := (710841063967541/500000000000000000000000000000000000000000000)

theorem directions : DirectionCheck 33 lineAt := by native_decide
theorem simple : SimpleCheck 33 lo hi 15 lineAt := by native_decide
theorem triangle_checks :
    triangles.all (fun t => decide (TriangleCheck 33 lo hi lineAt t))=true := by native_decide
theorem distinguished_checks :
    distinguished.all (fun t => decide (TriangleCheck 33 lo hi lineAt t))=true := by native_decide
theorem ordered : Increasing 33 triangles := by native_decide
theorem admissible_check : AdmissibleCheck 33 lineAt 10 (-13) := by native_decide
theorem visible_checks :
    visible.all (fun t => decide (VisibleCheck 33 lo hi lineAt 10 (-13) t))=true := by native_decide

noncomputable def parameters (epsilon : ℝ) : Fin 16 → ℝ :=
  ![tan (1*π/32),tan (2*π/32),tan (3*π/32),tan (4*π/32),tan (5*π/32),tan (6*π/32),tan (7*π/32),tan (8*π/32),tan (9*π/32),tan (10*π/32),tan (11*π/32),tan (12*π/32),tan (13*π/32),tan (14*π/32),tan (15*π/32),epsilon]

noncomputable def arrangement (epsilon : ℝ) (i : Nat) : Line ℝ :=
  toLine (lineAt i) (parameters epsilon)

theorem parameters_in_box (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000) :
    InBox lo hi (parameters epsilon) := by
  intro i
  fin_cases i
  · have h := TamuraTangentBounds.tan_32_1_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := TamuraTangentBounds.tan_32_2_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := TamuraTangentBounds.tan_32_3_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := TamuraTangentBounds.tan_32_4_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := TamuraTangentBounds.tan_32_5_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := TamuraTangentBounds.tan_32_6_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := TamuraTangentBounds.tan_32_7_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := TamuraTangentBounds.tan_32_8_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := TamuraTangentBounds.tan_32_9_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := TamuraTangentBounds.tan_32_10_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := TamuraTangentBounds.tan_32_11_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := TamuraTangentBounds.tan_32_12_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := TamuraTangentBounds.tan_32_13_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := TamuraTangentBounds.tan_32_14_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := TamuraTangentBounds.tan_32_15_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · simpa [lo,hi,parameters] using And.intro (le_of_lt he) hu

theorem no_parallel (epsilon : ℝ) : NoParallel 33 (arrangement epsilon) :=
  directions_sound 33 lineAt (parameters epsilon) directions

theorem no_concurrent (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000) :
    NoConcurrent 33 (arrangement epsilon) := by
  exact simple_sound 33 lo hi 15 lineAt (parameters epsilon)
    (parameters_in_box epsilon he hu) (by simpa [parameters] using he) simple

theorem all_triangles (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000)
    (t : Triple) (ht : t∈triangles) : TrianglePredicate 33 (arrangement epsilon) t := by
  have hc := triangle_checks
  simp only [List.all_eq_true,decide_eq_true_eq] at hc
  exact triangle_sound 33 lo hi 15 lineAt (parameters epsilon)
    (parameters_in_box epsilon he hu) (by simpa [parameters] using he) simple t (hc t ht)

theorem all_visible (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000)
    (t : Triple) (ht : t∈visible) :
    VisiblePair 33 (arrangement epsilon) (normalLine 10 (-13)) t := by
  have hc := visible_checks
  simp only [List.all_eq_true,decide_eq_true_eq] at hc
  exact visible_sound 33 lo hi lineAt 10 (-13) (parameters epsilon)
    (parameters_in_box epsilon he hu) directions admissible_check t (hc t ht)

theorem all_distinguished (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000)
    (t : Triple) (ht : t∈distinguished) : TrianglePredicate 33 (arrangement epsilon) t := by
  have hc := distinguished_checks
  simp only [List.all_eq_true,decide_eq_true_eq] at hc
  exact triangle_sound 33 lo hi 15 lineAt (parameters epsilon)
    (parameters_in_box epsilon he hu) (by simpa [parameters] using he) simple t (hc t ht)

theorem distinguished_count : distinguished.length=31 ∧ distinguished.Nodup := by decide +kernel
theorem visible_count : visible.length=16 ∧ visible.Nodup := by decide +kernel

theorem zero_line (epsilon : ℝ) : arrangement epsilon 0=graphLine 0 0 := by
  norm_num [arrangement,toLine,lineAt,lines,graphLine,evaluate,Fin.sum_univ_succ]

theorem last_line (epsilon : ℝ) :
    arrangement epsilon 32=graphLine rightSlope (tan (15*π/32)) := by
  norm_num [arrangement,toLine,lineAt,lines,graphLine,evaluate,Fin.sum_univ_succ,
    rightSlope,parameters]

theorem right_slope_positive : (0:ℝ)<rightSlope := by norm_num [rightSlope]
theorem right_slope_small : (rightSlope:ℝ)<10/13 := by norm_num [rightSlope]

theorem last_intersection (epsilon : ℝ) :
    intersection (arrangement epsilon 0) (arrangement epsilon 32)=(tan (15*π/32),0) := by
  rw [zero_line,last_line]
  have hm : (rightSlope:ℝ) ≠ 0 := ne_of_gt right_slope_positive
  simp [intersection,vertex,graphLine,det,hm]

theorem rightmost_last (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000)
    (r : Fin 33) (hr : r.val ≠ 32) :
    (intersection (arrangement epsilon 32) (arrangement epsilon r)).1≤tan (15*π/32) := by
  let L := arrangement epsilon
  let w := normalLine 10 (-13)
  have hp := no_parallel epsilon
  have hw : Admissible 33 L w := admissible_sound 33 lineAt 10 (-13) (parameters epsilon) admissible_check
  have hv : VisiblePair 33 L w ⟨0,32,33⟩ := all_visible epsilon he hu _ (by simp [visible])
  have hle := visible_extremal_right 33 L w hp hw ⟨0,32,33⟩ hv r hr
  have hdr : det (L 32) (L r) ≠ 0 := det_ne_of_ne 33 L hp ⟨32,by decide⟩ r (by
    intro hh
    exact hr (congrArg Fin.val hh).symm)
  have hdp : det (L 0) (L 32) ≠ 0 := hp ⟨0,by decide⟩ ⟨32,by decide⟩ (by decide)
  have hpr := intersection_on_left (L 32) (L r) hdr
  have hpp := intersection_on_right (L 0) (L 32) hdp
  have hlast : L 32=graphLine rightSlope (tan (15*π/32)) := last_line epsilon
  have hpr' : affineEval (graphLine rightSlope (tan (15*π/32))) (intersection (L 32) (L r))=0 := by
    rw [← hlast]
    exact hpr
  have hpp' : affineEval (graphLine rightSlope (tan (15*π/32))) (intersection (L 0) (L 32))=0 := by
    rw [← hlast]
    exact hpp
  have hdir : 0<w.a+w.b*(rightSlope:ℝ) := by
    dsimp [w,normalLine]
    norm_num [rightSlope]
  have hh := graph_projection_order rightSlope (tan (15*π/32)) w _ _ hpr' hpp' hdir hle
  simpa only [L,last_intersection,Prod.fst] using hh

theorem simple_lower_bound (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000) :
    SimpleLowerBound 33 341 := by
  exact ⟨arrangement epsilon,no_parallel epsilon,no_concurrent epsilon he hu,
    triangles,increasing_nodup 33 triangles ordered,all_triangles epsilon he hu,by decide⟩

theorem exterior_lower_bound (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000) :
    SimpleLowerBound 34 357 := by
  let L := arrangement epsilon
  let w := normalLine 10 (-13)
  have hw : Admissible 33 L w := admissible_sound 33 lineAt 10 (-13) (parameters epsilon) admissible_check
  have h := Exterior.extension 33 341 L triangles visible w (safeHeight 33 L w)
    (no_parallel epsilon) (no_concurrent epsilon he hu)
    (increasing_nodup 33 triangles ordered) (all_triangles epsilon he hu) (by decide)
    (by decide +kernel) (all_visible epsilon he hu) hw (safeHeight_beyond 33 L w)
  simpa [visible] using h

theorem arbitrarily_small (eta : ℝ) (heta : 0<eta) :
    ∃ epsilon : ℝ, 0<epsilon ∧ epsilon<eta ∧ epsilon≤1/100000 ∧
      NoConcurrent 33 (arrangement epsilon) ∧
      (∀ t∈triangles, TrianglePredicate 33 (arrangement epsilon) t) ∧
      (∀ t∈visible, VisiblePair 33 (arrangement epsilon) (normalLine 10 (-13)) t) := by
  let epsilon := min (eta/2) (1/100000:ℝ)
  have he : 0<epsilon := lt_min (by linarith) (by norm_num)
  have hu : epsilon≤1/100000 := min_le_right _ _
  have hl : epsilon<eta := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  exact ⟨epsilon,he,hl,hu,no_concurrent epsilon he hu,all_triangles epsilon he hu,all_visible epsilon he hu⟩

#print axioms simple_lower_bound
#print axioms exterior_lower_bound
#print axioms arbitrarily_small
#print axioms rightmost_last
end Kobon.TamuraSeed33
