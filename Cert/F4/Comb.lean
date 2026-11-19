import Cert.AssembleN
import Cert.F4.M0
import Cert.F4.M1

set_option maxRecDepth 100000
set_option linter.all false
set_option linter.unusedVariables false

namespace SuperpermLowerBounds
namespace Cert
namespace F4

/-- The whole search below a prefix does not find. -/
abbrev FC := FullC cd mk fN fS ct wrecT true

theorem hoff : ∀ t d, t < 5 → d < 61 → 16 * d + 2 * 30 * t + 30 ≤ offN := by
  intro t d ht hd
  simp only [offN]
  omega

theorem fx994921 : FC n994921 := fullS_of_cut_ok hoff x994921 (allC_cons (fullS_of_ok hoff g1003295) (allC_nil _))

theorem fx986260 : FC n986260 := fullS_of_cut_ok hoff x986260 (allC_cons (fx994921) (allC_nil _))

theorem fx969053 : FC n969053 := fullS_of_cut_ok hoff x969053 (allC_cons (fx986260) (allC_nil _))

theorem fx956075 : FC n956075 := fullS_of_cut_ok hoff x956075 (allC_cons (fx969053) (allC_nil _))

theorem fx936400 : FC n936400 := fullS_of_cut_ok hoff x936400 (allC_cons (fullS_of_ok hoff g937767) (allC_cons (fx956075) (allC_nil _)))

theorem fx924322 : FC n924322 := fullS_of_cut_ok hoff x924322 (allC_cons (fx936400) (allC_nil _))

theorem fx907686 : FC n907686 := fullS_of_cut_ok hoff x907686 (allC_cons (fx924322) (allC_nil _))

theorem fx899575 : FC n899575 := fullS_of_cut_ok hoff x899575 (allC_cons (fx907686) (allC_nil _))

theorem fx831983 : FC n831983 := fullS_of_cut_ok hoff x831983 (allC_cons (fullS_of_ok hoff g847904) (allC_nil _))

theorem fx831534 : FC n831534 := fullS_of_cut_ok hoff x831534 (allC_cons (fx831983) (allC_cons (fullS_of_ok hoff g877250) (allC_cons (fx899575) (allC_nil _))))

theorem fx753994 : FC n753994 := fullS_of_cut_ok hoff x753994 (allC_cons (fullS_of_ok hoff g761957) (allC_nil _))

theorem fx745959 : FC n745959 := fullS_of_cut_ok hoff x745959 (allC_cons (fx753994) (allC_nil _))

theorem fx734142 : FC n734142 := fullS_of_cut_ok hoff x734142 (allC_cons (fx745959) (allC_nil _))

theorem fx709109 : FC n709109 := fullS_of_cut_ok hoff x709109 (allC_cons (fullS_of_ok hoff g709781) (allC_cons (fx734142) (allC_cons (fullS_of_ok hoff g797260) (allC_nil _))))

theorem fx663891 : FC n663891 := fullS_of_cut_ok hoff x663891 (allC_cons (fullS_of_ok hoff g676308) (allC_nil _))

theorem fx652625 : FC n652625 := fullS_of_cut_ok hoff x652625 (allC_cons (fx663891) (allC_nil _))

theorem fx640234 : FC n640234 := fullS_of_cut_ok hoff x640234 (allC_cons (fx652625) (allC_cons (fx709109) (allC_nil _)))

theorem fx626468 : FC n626468 := fullS_of_cut_ok hoff x626468 (allC_cons (fx640234) (allC_nil _))

theorem fx615725 : FC n615725 := fullS_of_cut_ok hoff x615725 (allC_cons (fx626468) (allC_nil _))

theorem fx604668 : FC n604668 := fullS_of_cut_ok hoff x604668 (allC_cons (fx615725) (allC_cons (fx831534) (allC_nil _)))

theorem fx577362 : FC n577362 := fullS_of_cut_ok hoff x577362 (allC_cons (fullS_of_ok hoff g578870) (allC_nil _))

theorem fx577058 : FC n577058 := fullS_of_cut_ok hoff x577058 (allC_cons (fx577362) (allC_cons (fx604668) (allC_nil _)))

theorem fx532623 : FC n532623 := fullS_of_cut_ok hoff x532623 (allC_cons (fullS_of_ok hoff g544196) (allC_nil _))

theorem fx523707 : FC n523707 := fullS_of_cut_ok hoff x523707 (allC_cons (fx532623) (allC_cons (fx577058) (allC_nil _)))

theorem fx458918 : FC n458918 := fullS_of_cut_ok hoff x458918 (allC_cons (fullS_of_ok hoff g472933) (allC_nil _))

theorem fx450804 : FC n450804 := fullS_of_cut_ok hoff x450804 (allC_cons (fx458918) (allC_nil _))

theorem fx433526 : FC n433526 := fullS_of_cut_ok hoff x433526 (allC_cons (fullS_of_ok hoff g433741) (allC_cons (fx450804) (allC_nil _)))

theorem fx393541 : FC n393541 := fullS_of_cut_ok hoff x393541 (allC_cons (fullS_of_ok hoff g404890) (allC_nil _))

theorem fx352622 : FC n352622 := fullS_of_cut_ok hoff x352622 (allC_cons (fullS_of_ok hoff g353254) (allC_nil _))

theorem fx324145 : FC n324145 := fullS_of_cut_ok hoff x324145 (allC_cons (fullS_of_ok hoff g335046) (allC_cons (fx352622) (allC_nil _)))

theorem fx313843 : FC n313843 := fullS_of_cut_ok hoff x313843 (allC_cons (fx324145) (allC_nil _))

theorem fx310514 : FC n310514 := fullS_of_cut_ok hoff x310514 (allC_cons (fx313843) (allC_cons (fx393541) (allC_cons (fx433526) (allC_nil _))))

theorem fx295555 : FC n295555 := fullS_of_cut_ok hoff x295555 (allC_cons (fx310514) (allC_cons (fx523707) (allC_nil _)))

theorem fx284341 : FC n284341 := fullS_of_cut_ok hoff x284341 (allC_cons (fx295555) (allC_nil _))

theorem fx249732 : FC n249732 := fullS_of_cut_ok hoff x249732 (allC_cons (fullS_of_ok hoff g265008) (allC_cons (fx284341) (allC_nil _)))

theorem fx207561 : FC n207561 := fullS_of_cut_ok hoff x207561 (allC_cons (fullS_of_ok hoff g221074) (allC_nil _))

theorem fx125565 : FC n125565 := fullS_of_cut_ok hoff x125565 (allC_cons (fullS_of_ok hoff g129476) (allC_cons (fullS_of_ok hoff g145687) (allC_cons (fullS_of_ok hoff g164180) (allC_nil _))))

theorem fx120057 : FC n120057 := fullS_of_cut_ok hoff x120057 (allC_cons (fx125565) (allC_cons (fullS_of_ok hoff g184573) (allC_cons (fx207561) (allC_nil _))))

theorem fx37241 : FC n37241 := fullS_of_cut_ok hoff x37241 (allC_cons (fullS_of_ok hoff g44961) (allC_nil _))

theorem fx37240 : FC n37240 := fullS_of_cut_ok hoff x37240 (allC_cons (fx37241) (allC_cons (fullS_of_ok hoff g76362) (allC_cons (fullS_of_ok hoff g98778) (allC_cons (fx120057) (allC_cons (fx249732) (allC_nil _))))))

theorem fx13671 : FC n13671 := fullS_of_cut_ok hoff x13671 (allC_cons (fullS_of_ok hoff g24918) (allC_nil _))

/-- The whole search of F4 does not find. -/
theorem ok : searchC cd mk fN fS ct wrecT true wsT 400 [] ≠ none :=
  searchN_ok hoff top (allC_cons (fx13671) (allC_cons (fx37240) (allC_nil _)))

end F4
end Cert
end SuperpermLowerBounds
