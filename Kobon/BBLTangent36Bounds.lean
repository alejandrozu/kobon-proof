import Kobon.BBLRationalTangentBounds

/-! Actual denominator-36 tangent bounds. Candidate endpoints are generated
externally, but all Taylor remainder conditions are checked in the kernel.
The final endpoints match the exact interval certificate of the 37-line seed. -/
namespace Kobon.BBLTangent36Bounds
open Real BBLRationalTangentBounds
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def quarterLo1 : ℚ := ((218200776221494750131:ℚ)/10000000000000000000000)
def quarterHi1 : ℚ := ((54550194055373687583:ℚ)/2500000000000000000000)
theorem quarter_check_1 : QuarterCheck 36 1 16 quarterLo1 quarterHi1 := by
  decide +kernel

theorem tan_1_bounds : ((4374433176296150261:ℝ)/50000000000000000000)≤tan (1*π/36) ∧
    tan (1*π/36)≤((8748866352592500523:ℝ)/100000000000000000000) := by
  obtain ⟨hl,hu⟩ := quarterCheck_sound quarter_check_1
  have low : (((4374433176296150261:ℚ)/50000000000000000000):ℝ)≤(twiceRat (twiceRat quarterLo1):ℝ) := by
    exact_mod_cast (show ((4374433176296150261:ℚ)/50000000000000000000)≤twiceRat (twiceRat quarterLo1) by decide +kernel)
  have high : (twiceRat (twiceRat quarterHi1):ℝ)≤(((8748866352592500523:ℚ)/100000000000000000000):ℝ) := by
    exact_mod_cast (show twiceRat (twiceRat quarterHi1)≤((8748866352592500523:ℚ)/100000000000000000000) by decide +kernel)
  constructor
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using low.trans hl
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using hu.trans high

def quarterLo2 : ℚ := ((436609429085120619283:ℚ)/10000000000000000000000)
def quarterHi2 : ℚ := ((109152357271280154871:ℚ)/2500000000000000000000)
theorem quarter_check_2 : QuarterCheck 36 2 16 quarterLo2 quarterHi2 := by
  decide +kernel

theorem tan_2_bounds : ((17632698070846397347:ℝ)/100000000000000000000)≤tan (2*π/36) ∧
    tan (2*π/36)≤((4408174517711649337:ℝ)/25000000000000000000) := by
  obtain ⟨hl,hu⟩ := quarterCheck_sound quarter_check_2
  have low : (((17632698070846397347:ℚ)/100000000000000000000):ℝ)≤(twiceRat (twiceRat quarterLo2):ℝ) := by
    exact_mod_cast (show ((17632698070846397347:ℚ)/100000000000000000000)≤twiceRat (twiceRat quarterLo2) by decide +kernel)
  have high : (twiceRat (twiceRat quarterHi2):ℝ)≤(((4408174517711649337:ℚ)/25000000000000000000):ℝ) := by
    exact_mod_cast (show twiceRat (twiceRat quarterHi2)≤((4408174517711649337:ℚ)/25000000000000000000) by decide +kernel)
  constructor
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using low.trans hl
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using hu.trans high

def quarterLo3 : ℚ := ((131086925630476457109:ℚ)/2000000000000000000000)
def quarterHi3 : ℚ := ((327717314076191142873:ℚ)/5000000000000000000000)
theorem quarter_check_3 : QuarterCheck 36 3 16 quarterLo3 quarterHi3 := by
  decide +kernel

theorem tan_3_bounds : ((26794919243112170647:ℝ)/100000000000000000000)≤tan (3*π/36) ∧
    tan (3*π/36)≤((3349364905389046331:ℝ)/12500000000000000000) := by
  obtain ⟨hl,hu⟩ := quarterCheck_sound quarter_check_3
  have low : (((26794919243112170647:ℚ)/100000000000000000000):ℝ)≤(twiceRat (twiceRat quarterLo3):ℝ) := by
    exact_mod_cast (show ((26794919243112170647:ℚ)/100000000000000000000)≤twiceRat (twiceRat quarterLo3) by decide +kernel)
  have high : (twiceRat (twiceRat quarterHi3):ℝ)≤(((3349364905389046331:ℚ)/12500000000000000000):ℝ) := by
    exact_mod_cast (show twiceRat (twiceRat quarterHi3)≤((3349364905389046331:ℚ)/12500000000000000000) by decide +kernel)
  constructor
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using low.trans hl
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using hu.trans high

def quarterLo4 : ℚ := ((21872165881481001303:ℚ)/250000000000000000000)
def quarterHi4 : ℚ := ((874886635259240052321:ℚ)/10000000000000000000000)
theorem quarter_check_4 : QuarterCheck 36 4 16 quarterLo4 quarterHi4 := by
  decide +kernel

theorem tan_4_bounds : ((7279404685324027227:ℝ)/20000000000000000000)≤tan (4*π/36) ∧
    tan (4*π/36)≤((4549627928327542017:ℝ)/12500000000000000000) := by
  obtain ⟨hl,hu⟩ := quarterCheck_sound quarter_check_4
  have low : (((7279404685324027227:ℚ)/20000000000000000000):ℝ)≤(twiceRat (twiceRat quarterLo4):ℝ) := by
    exact_mod_cast (show ((7279404685324027227:ℚ)/20000000000000000000)≤twiceRat (twiceRat quarterLo4) by decide +kernel)
  have high : (twiceRat (twiceRat quarterHi4):ℝ)≤(((4549627928327542017:ℚ)/12500000000000000000):ℝ) := by
    exact_mod_cast (show twiceRat (twiceRat quarterHi4)≤((4549627928327542017:ℚ)/12500000000000000000) by decide +kernel)
  constructor
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using low.trans hl
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using hu.trans high

def quarterLo5 : ℚ := ((68448632302025910519:ℚ)/625000000000000000000)
def quarterHi5 : ℚ := ((219035623366482913701:ℚ)/2000000000000000000000)
theorem quarter_check_5 : QuarterCheck 36 5 16 quarterLo5 quarterHi5 := by
  decide +kernel

theorem tan_5_bounds : ((46630765815499759283:ℝ)/100000000000000000000)≤tan (5*π/36) ∧
    tan (5*π/36)≤((11657691453874989821:ℝ)/25000000000000000000) := by
  obtain ⟨hl,hu⟩ := quarterCheck_sound quarter_check_5
  have low : (((46630765815499759283:ℚ)/100000000000000000000):ℝ)≤(twiceRat (twiceRat quarterLo5):ℝ) := by
    exact_mod_cast (show ((46630765815499759283:ℚ)/100000000000000000000)≤twiceRat (twiceRat quarterLo5) by decide +kernel)
  have high : (twiceRat (twiceRat quarterHi5):ℝ)≤(((11657691453874989821:ℚ)/25000000000000000000):ℝ) := by
    exact_mod_cast (show twiceRat (twiceRat quarterHi5)≤((11657691453874989821:ℚ)/25000000000000000000) by decide +kernel)
  constructor
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using low.trans hl
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using hu.trans high

def quarterLo6 : ℚ := ((263304995174791706923:ℚ)/2000000000000000000000)
def quarterHi6 : ℚ := ((41141405496061204213:ℚ)/312500000000000000000)
theorem quarter_check_6 : QuarterCheck 36 6 16 quarterLo6 quarterHi6 := by
  decide +kernel

theorem tan_6_bounds : ((1154700538379249529:ℝ)/2000000000000000000)≤tan (6*π/36) ∧
    tan (6*π/36)≤((57735026918962676451:ℝ)/100000000000000000000) := by
  obtain ⟨hl,hu⟩ := quarterCheck_sound quarter_check_6
  have low : (((1154700538379249529:ℚ)/2000000000000000000):ℝ)≤(twiceRat (twiceRat quarterLo6):ℝ) := by
    exact_mod_cast (show ((1154700538379249529:ℚ)/2000000000000000000)≤twiceRat (twiceRat quarterLo6) by decide +kernel)
  have high : (twiceRat (twiceRat quarterHi6):ℝ)≤(((57735026918962676451:ℚ)/100000000000000000000):ℝ) := by
    exact_mod_cast (show twiceRat (twiceRat quarterHi6)≤((57735026918962676451:ℚ)/100000000000000000000) by decide +kernel)
  constructor
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using low.trans hl
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using hu.trans high

def quarterLo7 : ℚ := ((1539147210598290523843:ℚ)/10000000000000000000000)
def quarterHi7 : ℚ := ((384786802649572631011:ℚ)/2500000000000000000000)
theorem quarter_check_7 : QuarterCheck 36 7 16 quarterLo7 quarterHi7 := by
  decide +kernel

theorem tan_7_bounds : ((14004150764194175589:ℝ)/20000000000000000000)≤tan (7*π/36) ∧
    tan (7*π/36)≤((35010376910485538973:ℝ)/50000000000000000000) := by
  obtain ⟨hl,hu⟩ := quarterCheck_sound quarter_check_7
  have low : (((14004150764194175589:ℚ)/20000000000000000000):ℝ)≤(twiceRat (twiceRat quarterLo7):ℝ) := by
    exact_mod_cast (show ((14004150764194175589:ℚ)/20000000000000000000)≤twiceRat (twiceRat quarterLo7) by decide +kernel)
  have high : (twiceRat (twiceRat quarterHi7):ℝ)≤(((35010376910485538973:ℚ)/50000000000000000000):ℝ) := by
    exact_mod_cast (show twiceRat (twiceRat quarterHi7)≤((35010376910485538973:ℚ)/50000000000000000000) by decide +kernel)
  constructor
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using low.trans hl
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using hu.trans high

def quarterLo8 : ℚ := ((176326980708464973461:ℚ)/1000000000000000000000)
def quarterHi8 : ℚ := ((1763269807084649734811:ℚ)/10000000000000000000000)
theorem quarter_check_8 : QuarterCheck 36 8 16 quarterLo8 quarterHi8 := by
  decide +kernel

theorem tan_8_bounds : ((10488745389715987647:ℝ)/12500000000000000000)≤tan (8*π/36) ∧
    tan (8*π/36)≤((83909963117728101177:ℝ)/100000000000000000000) := by
  obtain ⟨hl,hu⟩ := quarterCheck_sound quarter_check_8
  have low : (((10488745389715987647:ℚ)/12500000000000000000):ℝ)≤(twiceRat (twiceRat quarterLo8):ℝ) := by
    exact_mod_cast (show ((10488745389715987647:ℚ)/12500000000000000000)≤twiceRat (twiceRat quarterLo8) by decide +kernel)
  have high : (twiceRat (twiceRat quarterHi8):ℝ)≤(((83909963117728101177:ℚ)/100000000000000000000):ℝ) := by
    exact_mod_cast (show twiceRat (twiceRat quarterHi8)≤((83909963117728101177:ℚ)/100000000000000000000) by decide +kernel)
  constructor
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using low.trans hl
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using hu.trans high

def quarterLo9 : ℚ := ((397824734759316013803:ℚ)/2000000000000000000000)
def quarterHi9 : ℚ := ((62160114806143127163:ℚ)/312500000000000000000)
theorem quarter_check_9 : QuarterCheck 36 9 16 quarterLo9 quarterHi9 := by
  decide +kernel

theorem tan_9_bounds : ((999999999999999:ℝ)/1000000000000000)≤tan (9*π/36) ∧
    tan (9*π/36)≤((1000000000000001:ℝ)/1000000000000000) := by
  obtain ⟨hl,hu⟩ := quarterCheck_sound quarter_check_9
  have low : (((999999999999999:ℚ)/1000000000000000):ℝ)≤(twiceRat (twiceRat quarterLo9):ℝ) := by
    exact_mod_cast (show ((999999999999999:ℚ)/1000000000000000)≤twiceRat (twiceRat quarterLo9) by decide +kernel)
  have high : (twiceRat (twiceRat quarterHi9):ℝ)≤(((1000000000000001:ℚ)/1000000000000000):ℝ) := by
    exact_mod_cast (show twiceRat (twiceRat quarterHi9)≤((1000000000000001:ℚ)/1000000000000000) by decide +kernel)
  constructor
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using low.trans hl
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using hu.trans high

def quarterLo10 : ℚ := ((1108473313214699507837:ℚ)/5000000000000000000000)
def quarterHi10 : ℚ := ((17735573011435192127:ℚ)/80000000000000000000)
theorem quarter_check_10 : QuarterCheck 36 10 16 quarterLo10 quarterHi10 := by
  decide +kernel

theorem tan_10_bounds : ((11917535925942089587:ℝ)/10000000000000000000)≤tan (10*π/36) ∧
    tan (10*π/36)≤((119175359259421095871:ℝ)/100000000000000000000) := by
  obtain ⟨hl,hu⟩ := quarterCheck_sound quarter_check_10
  have low : (((11917535925942089587:ℚ)/10000000000000000000):ℝ)≤(twiceRat (twiceRat quarterLo10):ℝ) := by
    exact_mod_cast (show ((11917535925942089587:ℚ)/10000000000000000000)≤twiceRat (twiceRat quarterLo10) by decide +kernel)
  have high : (twiceRat (twiceRat quarterHi10):ℝ)≤(((119175359259421095871:ℚ)/100000000000000000000):ℝ) := by
    exact_mod_cast (show twiceRat (twiceRat quarterHi10)≤((119175359259421095871:ℚ)/100000000000000000000) by decide +kernel)
  constructor
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using low.trans hl
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using hu.trans high

def quarterLo11 : ℚ := ((1223492216145171853781:ℚ)/5000000000000000000000)
def quarterHi11 : ℚ := ((2446984432290343707763:ℚ)/10000000000000000000000)
theorem quarter_check_11 : QuarterCheck 36 11 16 quarterLo11 quarterHi11 := by
  decide +kernel

theorem tan_11_bounds : ((17851850084276418777:ℝ)/12500000000000000000)≤tan (11*π/36) ∧
    tan (11*π/36)≤((142814800674211550217:ℝ)/100000000000000000000) := by
  obtain ⟨hl,hu⟩ := quarterCheck_sound quarter_check_11
  have low : (((17851850084276418777:ℚ)/12500000000000000000):ℝ)≤(twiceRat (twiceRat quarterLo11):ℝ) := by
    exact_mod_cast (show ((17851850084276418777:ℚ)/12500000000000000000)≤twiceRat (twiceRat quarterLo11) by decide +kernel)
  have high : (twiceRat (twiceRat quarterHi11):ℝ)≤(((142814800674211550217:ℚ)/100000000000000000000):ℝ) := by
    exact_mod_cast (show twiceRat (twiceRat quarterHi11)≤((142814800674211550217:ℚ)/100000000000000000000) by decide +kernel)
  constructor
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using low.trans hl
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using hu.trans high

def quarterLo12 : ℚ := ((21435935394489816517:ℚ)/80000000000000000000)
def quarterHi12 : ℚ := ((1339745962155613532413:ℚ)/5000000000000000000000)
theorem quarter_check_12 : QuarterCheck 36 12 16 quarterLo12 quarterHi12 := by
  decide +kernel

theorem tan_12_bounds : ((21650635094610953669:ℝ)/12500000000000000000)≤tan (12*π/36) ∧
    tan (12*π/36)≤((173205080756887829353:ℝ)/100000000000000000000) := by
  obtain ⟨hl,hu⟩ := quarterCheck_sound quarter_check_12
  have low : (((21650635094610953669:ℚ)/12500000000000000000):ℝ)≤(twiceRat (twiceRat quarterLo12):ℝ) := by
    exact_mod_cast (show ((21650635094610953669:ℚ)/12500000000000000000)≤twiceRat (twiceRat quarterLo12) by decide +kernel)
  have high : (twiceRat (twiceRat quarterHi12):ℝ)≤(((173205080756887829353:ℚ)/100000000000000000000):ℝ) := by
    exact_mod_cast (show twiceRat (twiceRat quarterHi12)≤((173205080756887829353:ℚ)/100000000000000000000) by decide +kernel)
  constructor
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using low.trans hl
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using hu.trans high

def quarterLo13 : ℚ := ((728683548965218910327:ℚ)/2500000000000000000000)
def quarterHi13 : ℚ := ((2914734195860875641509:ℚ)/10000000000000000000000)
theorem quarter_check_13 : QuarterCheck 36 13 16 quarterLo13 quarterHi13 := by
  decide +kernel

theorem tan_13_bounds : ((42890138410191152327:ℝ)/20000000000000000000)≤tan (13*π/36) ∧
    tan (13*π/36)≤((53612673012738990409:ℝ)/25000000000000000000) := by
  obtain ⟨hl,hu⟩ := quarterCheck_sound quarter_check_13
  have low : (((42890138410191152327:ℚ)/20000000000000000000):ℝ)≤(twiceRat (twiceRat quarterLo13):ℝ) := by
    exact_mod_cast (show ((42890138410191152327:ℚ)/20000000000000000000)≤twiceRat (twiceRat quarterLo13) by decide +kernel)
  have high : (twiceRat (twiceRat quarterHi13):ℝ)≤(((53612673012738990409:ℚ)/25000000000000000000):ℝ) := by
    exact_mod_cast (show twiceRat (twiceRat quarterHi13)≤((53612673012738990409:ℚ)/25000000000000000000) by decide +kernel)
  constructor
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using low.trans hl
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using hu.trans high

def quarterLo14 : ℚ := ((315298788878983517667:ℚ)/1000000000000000000000)
def quarterHi14 : ℚ := ((3152987888789835176871:ℚ)/10000000000000000000000)
theorem quarter_check_14 : QuarterCheck 36 14 16 quarterLo14 quarterHi14 := by
  decide +kernel

theorem tan_14_bounds : ((68686935486365531969:ℝ)/25000000000000000000)≤tan (14*π/36) ∧
    tan (14*π/36)≤((274747741945462327877:ℝ)/100000000000000000000) := by
  obtain ⟨hl,hu⟩ := quarterCheck_sound quarter_check_14
  have low : (((68686935486365531969:ℚ)/25000000000000000000):ℝ)≤(twiceRat (twiceRat quarterLo14):ℝ) := by
    exact_mod_cast (show ((68686935486365531969:ℚ)/25000000000000000000)≤twiceRat (twiceRat quarterLo14) by decide +kernel)
  have high : (twiceRat (twiceRat quarterHi14):ℝ)≤(((274747741945462327877:ℚ)/100000000000000000000):ℝ) := by
    exact_mod_cast (show twiceRat (twiceRat quarterHi14)≤((274747741945462327877:ℚ)/100000000000000000000) by decide +kernel)
  constructor
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using low.trans hl
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using hu.trans high

def quarterLo15 : ℚ := ((3394542588633758155271:ℚ)/10000000000000000000000)
def quarterHi15 : ℚ := ((212158911789609884717:ℚ)/625000000000000000000)
theorem quarter_check_15 : QuarterCheck 36 15 16 quarterLo15 quarterHi15 := by
  decide +kernel

theorem tan_15_bounds : ((46650635094610953669:ℝ)/12500000000000000000)≤tan (15*π/36) ∧
    tan (15*π/36)≤((373205080756887829353:ℝ)/100000000000000000000) := by
  obtain ⟨hl,hu⟩ := quarterCheck_sound quarter_check_15
  have low : (((46650635094610953669:ℚ)/12500000000000000000):ℝ)≤(twiceRat (twiceRat quarterLo15):ℝ) := by
    exact_mod_cast (show ((46650635094610953669:ℚ)/12500000000000000000)≤twiceRat (twiceRat quarterLo15) by decide +kernel)
  have high : (twiceRat (twiceRat quarterHi15):ℝ)≤(((373205080756887829353:ℚ)/100000000000000000000):ℝ) := by
    exact_mod_cast (show twiceRat (twiceRat quarterHi15)≤((373205080756887829353:ℚ)/100000000000000000000) by decide +kernel)
  constructor
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using low.trans hl
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using hu.trans high

def quarterLo16 : ℚ := ((363970234266202361341:ℚ)/1000000000000000000000)
def quarterHi16 : ℚ := ((3639702342662023613611:ℚ)/10000000000000000000000)
theorem quarter_check_16 : QuarterCheck 36 16 16 quarterLo16 quarterHi16 := by
  decide +kernel

theorem tan_16_bounds : ((567128181961770853099:ℝ)/100000000000000000000)≤tan (16*π/36) ∧
    tan (16*π/36)≤((5671281819617710531:ℝ)/1000000000000000000) := by
  obtain ⟨hl,hu⟩ := quarterCheck_sound quarter_check_16
  have low : (((567128181961770853099:ℚ)/100000000000000000000):ℝ)≤(twiceRat (twiceRat quarterLo16):ℝ) := by
    exact_mod_cast (show ((567128181961770853099:ℚ)/100000000000000000000)≤twiceRat (twiceRat quarterLo16) by decide +kernel)
  have high : (twiceRat (twiceRat quarterHi16):ℝ)≤(((5671281819617710531:ℚ)/1000000000000000000):ℝ) := by
    exact_mod_cast (show twiceRat (twiceRat quarterHi16)≤((5671281819617710531:ℚ)/1000000000000000000) by decide +kernel)
  constructor
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using low.trans hl
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using hu.trans high

def quarterLo17 : ℚ := ((388878731852989668239:ℚ)/1000000000000000000000)
def quarterHi17 : ℚ := ((3888787318529896682591:ℚ)/10000000000000000000000)
theorem quarter_check_17 : QuarterCheck 36 17 16 quarterLo17 quarterHi17 := by
  decide +kernel

theorem tan_17_bounds : ((1143005230276134206721:ℝ)/100000000000000000000)≤tan (17*π/36) ∧
    tan (17*π/36)≤((571502615138067203361:ℝ)/50000000000000000000) := by
  obtain ⟨hl,hu⟩ := quarterCheck_sound quarter_check_17
  have low : (((1143005230276134206721:ℚ)/100000000000000000000):ℝ)≤(twiceRat (twiceRat quarterLo17):ℝ) := by
    exact_mod_cast (show ((1143005230276134206721:ℚ)/100000000000000000000)≤twiceRat (twiceRat quarterLo17) by decide +kernel)
  have high : (twiceRat (twiceRat quarterHi17):ℝ)≤(((571502615138067203361:ℚ)/50000000000000000000):ℝ) := by
    exact_mod_cast (show twiceRat (twiceRat quarterHi17)≤((571502615138067203361:ℚ)/50000000000000000000) by decide +kernel)
  constructor
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using low.trans hl
  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using hu.trans high

#print axioms tan_1_bounds
#print axioms tan_17_bounds
end Kobon.BBLTangent36Bounds
