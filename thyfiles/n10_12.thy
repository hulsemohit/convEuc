theory n10_12
	imports Axioms Definitions Theorems
begin

theorem n10_12:
	assumes: `axioms`
		"ang_right A B C"
		"ang_right A B H"
		"seg_eq B C B H"
	shows: "seg_eq A C A H"
proof -
	obtain D where "bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C" using rightangle_f[OF `axioms` `ang_right A B C`] by blast
	have "bet A B D" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
	have "seg_eq A B D B" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
	obtain F where "bet A B F \<and> seg_eq A B F B \<and> seg_eq A H F H \<and> B \<noteq> H" using rightangle_f[OF `axioms` `ang_right A B H`] by blast
	have "bet A B F" using `bet A B F \<and> seg_eq A B F B \<and> seg_eq A H F H \<and> B \<noteq> H` by blast
	have "seg_eq A B F B" using `bet A B F \<and> seg_eq A B F B \<and> seg_eq A H F H \<and> B \<noteq> H` by blast
	have "seg_eq A H F H" using `bet A B F \<and> seg_eq A B F B \<and> seg_eq A H F H \<and> B \<noteq> H` by blast
	have "seg_eq D B A B" using congruencesymmetric[OF `axioms` `seg_eq A B D B`] .
	have "seg_eq D B F B" using congruencetransitive[OF `axioms` `seg_eq D B A B` `seg_eq A B F B`] .
	have "seg_eq B F B D" using doublereverse[OF `axioms` `seg_eq D B F B`] by blast
	have "F = D" using extensionunique[OF `axioms` `bet A B F` `bet A B D` `seg_eq B F B D`] .
	have "seg_eq A H D H" using `seg_eq A H F H` `F = D` by blast
	consider "C = H"|"C \<noteq> H" by blast
	hence seg_eq A C A H
	proof (cases)
		case 1
		have "seg_eq A C A C" using congruencereflexiveE[OF `axioms`] by blast
		have "seg_eq A C A H" using `seg_eq A C A C` `C = H` by blast
	next
		case 2
		obtain M where "bet C M H \<and> seg_eq M C M H" using Prop10[OF `axioms` `C \<noteq> H`] by blast
		have "bet C M H" using `bet C M H \<and> seg_eq M C M H` by blast
		have "seg_eq M C M H" using `bet C M H \<and> seg_eq M C M H` by blast
		have "seg_eq C B H B" using doublereverse[OF `axioms` `seg_eq B C B H`] by blast
		consider "B = M"|"B \<noteq> M" by blast
		hence seg_eq A C A H
		proof (cases)
			case 1
			have "ang_right A B C" using `ang_right A B C` .
			have "ang_right C B A" using n8_2[OF `axioms` `ang_right A B C`] .
			have "bet C B H" using `bet C M H` `B = M` by blast
			have "seg_eq M C M H" using `seg_eq M C M H` .
			have "seg_eq B C B H" using `seg_eq B C B H` by blast
			have "seg_eq C B B H" using congruenceflip[OF `axioms` `seg_eq B C B H`] by blast
			have "seg_eq C A H A" using rightreverse[OF `axioms` `ang_right C B A` `bet C B H` `seg_eq C B B H`] .
			have "seg_eq A C A H" using congruenceflip[OF `axioms` `seg_eq C A H A`] by blast
		next
			case 2
			have "M \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> M`] .
			have "bet C M H" using `bet C M H` .
			have "seg_eq C M H M" using congruenceflip[OF `axioms` `seg_eq M C M H`] by blast
			have "seg_eq C B H B" using `seg_eq C B H B` .
			have "ang_right C M B" using rightangle_b[OF `axioms` `bet C M H` `seg_eq C M H M` `seg_eq C B H B` `M \<noteq> B`] .
			have "ang_right B M C" using n8_2[OF `axioms` `ang_right C M B`] .
			have "seg_eq A C D C" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
			have "seg_eq A H D H" using `seg_eq A H D H` .
			have "bet C M H" using `bet C M H` .
			have "seg_eq C A C D" using congruenceflip[OF `axioms` `seg_eq A C D C`] by blast
			have "seg_eq H A H D" using congruenceflip[OF `axioms` `seg_eq A H D H`] by blast
			have "seg_eq C M C M" using congruencereflexiveE[OF `axioms`] by blast
			have "seg_eq M H M H" using congruencereflexiveE[OF `axioms`] by blast
			have "seg_eq M A M D" using interior5[OF `axioms` `bet C M H` `bet C M H` `seg_eq C M C M` `seg_eq M H M H` `seg_eq C A C D` `seg_eq H A H D`] .
			have "seg_eq A M D M" using congruenceflip[OF `axioms` `seg_eq M A M D`] by blast
			have "B \<noteq> M" using inequalitysymmetric[OF `axioms` `M \<noteq> B`] .
			have "bet A B D" using `bet A B D` .
			have "seg_eq A B D B" using `seg_eq A B D B` .
			have "seg_eq A M D M" using `seg_eq A M D M` .
			have "ang_right A B M" using rightangle_b[OF `axioms` `bet A B D` `seg_eq A B D B` `seg_eq A M D M` `B \<noteq> M`] .
			have "bet C M H" using `bet C M H` .
			have "seg_eq M C M H" using `seg_eq M C M H` .
			have "bet A B D" using `bet A B D` .
			have "seg_eq B A B D" using congruenceflip[OF `axioms` `seg_eq A B D B`] by blast
			have "ang_right M B A" using n8_2[OF `axioms` `ang_right A B M`] .
			have "ang_right B M C" using `ang_right B M C` .
			have "seg_eq C A H D" using linereflectionisometry[OF `axioms` `ang_right B M C` `ang_right M B A` `bet C M H` `bet A B D` `seg_eq M C M H` `seg_eq B A B D`] .
			have "seg_eq A C D H" using congruenceflip[OF `axioms` `seg_eq C A H D`] by blast
			have "ang_right A B H" using `ang_right A B H` .
			have "bet A B D" using `bet A B D` .
			have "seg_eq A B B D" using congruenceflip[OF `axioms` `seg_eq A B D B`] by blast
			have "seg_eq A H D H" using rightreverse[OF `axioms` `ang_right A B H` `bet A B D` `seg_eq A B B D`] .
			have "seg_eq D H A H" using congruencesymmetric[OF `axioms` `seg_eq A H D H`] .
			have "seg_eq C A H D" using congruenceflip[OF `axioms` `seg_eq A C D H`] by blast
			have "seg_eq H D H A" using congruenceflip[OF `axioms` `seg_eq D H A H`] by blast
			have "seg_eq C A H A" using congruencetransitive[OF `axioms` `seg_eq C A H D` `seg_eq H D H A`] .
			have "seg_eq A C A H" using congruenceflip[OF `axioms` `seg_eq C A H A`] by blast
		next
	next
	thus ?thesis by blast
qed

end