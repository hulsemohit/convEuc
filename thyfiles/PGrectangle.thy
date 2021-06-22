theory PGrectangle
	imports Axioms Definitions Theorems
begin

theorem PGrectangle:
	assumes: `axioms`
		"parallelogram A C D B"
		"ang_right B A C"
	shows: "rectangle A C D B"
proof -
	have "seg_eq A B C D \<and> seg_eq A C B D \<and> ang_eq C A B B D C \<and> ang_eq A B D D C A \<and> tri_cong C A B B D C" using Prop34[OF `axioms` `parallelogram A C D B`] .
	have "ang_eq C A B B D C" using `seg_eq A B C D \<and> seg_eq A C B D \<and> ang_eq C A B B D C \<and> ang_eq A B D D C A \<and> tri_cong C A B B D C` by blast
	have "ang_eq A B D D C A" using `seg_eq A B C D \<and> seg_eq A C B D \<and> ang_eq C A B B D C \<and> ang_eq A B D D C A \<and> tri_cong C A B B D C` by blast
	have "parallel A C D B" sorry
	have "\<not> col A C B" using parallelNC[OF `axioms` `parallel A C D B`] by blast
	have "\<not> col A B C" using NCorder[OF `axioms` `\<not> col A C B`] by blast
	have "\<not> col C A B" using NCorder[OF `axioms` `\<not> col A B C`] by blast
	have "ang_eq C A B B A C" using ABCequalsCBA[OF `axioms` `\<not> col C A B`] .
	have "ang_right C A B" using n8_2[OF `axioms` `ang_right B A C`] .
	have "A \<noteq> B" using NCdistinct[OF `axioms` `\<not> col A B C`] by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
	have "ang_eq B A C C A B" using equalanglessymmetric[OF `axioms` `ang_eq C A B B A C`] .
	have "ang_eq B A C B D C" using equalanglestransitive[OF `axioms` `ang_eq B A C C A B` `ang_eq C A B B D C`] .
	have "ang_eq B D C B A C" using equalanglessymmetric[OF `axioms` `ang_eq B A C B D C`] .
	have "ang_right B D C" using equaltorightisright[OF `axioms` `ang_right B A C` `ang_eq B D C B A C`] .
	have "ang_right C D B" using n8_2[OF `axioms` `ang_right B D C`] .
	have "parallel A C B D" using parallelflip[OF `axioms` `parallel A C D B`] by blast
	have "parallel A B C D" sorry
	have "tarski_parallel A B C D" using paralleldef2B[OF `axioms` `parallel A B C D`] .
	have "same_side C D A B" sorry
	obtain E where "bet B A E \<and> seg_eq A E A B" using extensionE[OF `axioms` `B \<noteq> A` `A \<noteq> B`]  by  blast
	have "bet B A E" using `bet B A E \<and> seg_eq A E A B` by blast
	have "bet E A B" using betweennesssymmetryE[OF `axioms` `bet B A E`] .
	have "ang_suppl C A B A B D" using Prop29C[OF `axioms` `parallel A C B D` `same_side C D A B` `bet E A B`] by blast
	obtain p q r s t where "linear_pair p q r s t \<and> ang_eq C A B p q r \<and> ang_eq A B D s q t" sorry
	have "linear_pair p q r s t" using `linear_pair p q r s t \<and> ang_eq C A B p q r \<and> ang_eq A B D s q t` by blast
	have "ang_eq C A B p q r" using `linear_pair p q r s t \<and> ang_eq C A B p q r \<and> ang_eq A B D s q t` by blast
	have "ang_eq A B D s q t" using `linear_pair p q r s t \<and> ang_eq C A B p q r \<and> ang_eq A B D s q t` by blast
	have "ang_eq p q r C A B" using equalanglessymmetric[OF `axioms` `ang_eq C A B p q r`] .
	have "ang_right p q r" using equaltorightisright[OF `axioms` `ang_right C A B` `ang_eq p q r C A B`] .
	have "ang_right s q t" using supplementofright[OF `axioms` `linear_pair p q r s t` `ang_right p q r`] by blast
	have "ang_right A B D" using equaltorightisright[OF `axioms` `ang_right s q t` `ang_eq A B D s q t`] .
	have "ang_right D B A" using n8_2[OF `axioms` `ang_right A B D`] .
	have "ang_eq D C A A B D" using equalanglessymmetric[OF `axioms` `ang_eq A B D D C A`] .
	have "ang_right D C A" using equaltorightisright[OF `axioms` `ang_right A B D` `ang_eq D C A A B D`] .
	have "ang_right A C D" using n8_2[OF `axioms` `ang_right D C A`] .
	obtain M where "bet A M D \<and> bet C M B" using diagonalsmeet[OF `axioms` `parallelogram A C D B`]  by  blast
	have "bet A M D" using `bet A M D \<and> bet C M B` by blast
	have "bet C M B" using `bet A M D \<and> bet C M B` by blast
	have "cross A D C B" sorry
	have "ang_right B A C \<and> ang_right A C D \<and> ang_right C D B \<and> ang_right D B A \<and> cross A D C B" using `ang_right B A C` `ang_right A C D` `ang_right C D B` `ang_right D B A` `cross A D C B` by blast
	have "rectangle A C D B" sorry
	thus ?thesis by blast
qed

end