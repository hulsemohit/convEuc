theory rectanglereverse
	imports Axioms Definitions Theorems
begin

theorem rectanglereverse:
	assumes: `axioms`
		"rectangle A B C D"
	shows: "rectangle D C B A"
proof -
	have "ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A \<and> cross A C B D" using rectangle_f[OF `axioms` `rectangle A B C D`] .
	have "ang_right D A B" using `ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A \<and> cross A C B D` by blast
	have "ang_right A B C" using `ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A \<and> cross A C B D` by blast
	have "ang_right B C D" using `ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A \<and> cross A C B D` by blast
	have "ang_right C D A" using `ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A \<and> cross A C B D` by blast
	have "cross A C B D" using `ang_right D A B \<and> ang_right A B C \<and> ang_right B C D \<and> ang_right C D A \<and> cross A C B D` by blast
	have "ang_right A D C" using n8_2[OF `axioms` `ang_right C D A`] .
	have "ang_right D C B" using n8_2[OF `axioms` `ang_right B C D`] .
	have "ang_right C B A" using n8_2[OF `axioms` `ang_right A B C`] .
	have "ang_right B A D" using n8_2[OF `axioms` `ang_right D A B`] .
	obtain M where "bet A M C \<and> bet B M D" using cross_f[OF `axioms` `cross A C B D`] by blast
	have "bet A M C" using `bet A M C \<and> bet B M D` by blast
	have "bet B M D" using `bet A M C \<and> bet B M D` by blast
	have "bet C M A" using betweennesssymmetryE[OF `axioms` `bet A M C`] .
	have "bet D M B" using betweennesssymmetryE[OF `axioms` `bet B M D`] .
	have "cross D B C A" using cross_b[OF `axioms` `bet D M B` `bet C M A`] .
	have "ang_right A D C \<and> ang_right D C B \<and> ang_right C B A \<and> ang_right B A D \<and> cross D B C A" using `ang_right A D C` `ang_right D C B` `ang_right C B A` `ang_right B A D` `cross D B C A` by blast
	have "rectangle D C B A" using rectangle_b[OF `axioms` `ang_right A D C` `ang_right D C B` `ang_right C B A` `ang_right B A D` `cross D B C A`] .
	thus ?thesis by blast
qed

end