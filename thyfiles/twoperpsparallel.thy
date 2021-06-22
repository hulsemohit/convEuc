theory twoperpsparallel
	imports Axioms Definitions Theorems
begin

theorem twoperpsparallel:
	assumes: `axioms`
		"ang_right A B C"
		"ang_right B C D"
		"same_side A D B C"
	shows: "parallel A B C D"
proof -
	have "\<not> col A B C" using rightangleNC[OF `axioms` `ang_right A B C`] .
	have "B \<noteq> C" using NCdistinct[OF `axioms` `\<not> col A B C`] by blast
	obtain E where "bet B C E \<and> seg_eq C E B C" using extensionE[OF `axioms` `B \<noteq> C` `B \<noteq> C`]  by  blast
	have "bet B C E" using `bet B C E \<and> seg_eq C E B C` by blast
	have "col B C E" using col_b `axioms` `bet B C E \<and> seg_eq C E B C` by blast
	have "C \<noteq> E" using betweennotequal[OF `axioms` `bet B C E`] by blast
	have "E \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> E`] .
	have "ang_right E C D" using collinearright[OF `axioms` `ang_right B C D` `col B C E` `E \<noteq> C`] .
	have "ang_right D C E" using n8_2[OF `axioms` `ang_right E C D`] .
	have "D = D" using equalityreflexiveE[OF `axioms`] .
	have "\<not> col B C D" using rightangleNC[OF `axioms` `ang_right B C D`] .
	have "C \<noteq> D" using NCdistinct[OF `axioms` `\<not> col B C D`] by blast
	have "ray_on C D D" using ray4 `axioms` `D = D` `C \<noteq> D` by blast
	have "linear_pair B C D D E" sorry
	have "ang_eq A B C B C D" using Euclid4[OF `axioms` `ang_right A B C` `ang_right B C D`] .
	have "ang_eq B C D D C E" using Euclid4[OF `axioms` `ang_right B C D` `ang_right D C E`] .
	have "ang_suppl A B C B C D" sorry
	have "parallel B A C D" using Prop28C[OF `axioms` `ang_suppl A B C B C D` `same_side A D B C`] .
	have "parallel C D B A" using parallelsymmetric[OF `axioms` `parallel B A C D`] .
	have "parallel C D A B" using parallelflip[OF `axioms` `parallel C D B A`] by blast
	have "parallel A B C D" using parallelsymmetric[OF `axioms` `parallel C D A B`] .
	thus ?thesis by blast
qed

end