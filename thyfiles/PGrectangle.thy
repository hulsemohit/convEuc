theory PGrectangle
	imports n8_2 ABCequalsCBA Geometry NCdistinct NCorder Prop29C Prop34 diagonalsmeet equalanglessymmetric equalanglestransitive equaltorightisright inequalitysymmetric parallelNC paralleldef2B parallelflip supplementofright
begin

theorem(in euclidean_geometry) PGrectangle:
	assumes 
		"parallelogram A C D B"
		"ang_right B A C"
	shows "rectangle A C D B"
proof -
	have "seg_eq A B C D \<and> seg_eq A C B D \<and> ang_eq C A B B D C \<and> ang_eq A B D D C A \<and> tri_cong C A B B D C" using Prop34[OF `parallelogram A C D B`] .
	have "ang_eq C A B B D C" using `seg_eq A B C D \<and> seg_eq A C B D \<and> ang_eq C A B B D C \<and> ang_eq A B D D C A \<and> tri_cong C A B B D C` by blast
	have "ang_eq A B D D C A" using `seg_eq A B C D \<and> seg_eq A C B D \<and> ang_eq C A B B D C \<and> ang_eq A B D D C A \<and> tri_cong C A B B D C` by blast
	have "parallel A C D B" using parallelogram_f[OF `parallelogram A C D B`] by blast
	have "\<not> col A C B" using parallelNC[OF `parallel A C D B`] by blast
	have "\<not> col A B C" using NCorder[OF `\<not> col A C B`] by blast
	have "\<not> col C A B" using NCorder[OF `\<not> col A B C`] by blast
	have "ang_eq C A B B A C" using ABCequalsCBA[OF `\<not> col C A B`] .
	have "ang_right C A B" using n8_2[OF `ang_right B A C`] .
	have "A \<noteq> B" using NCdistinct[OF `\<not> col A B C`] by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `A \<noteq> B`] .
	have "ang_eq B A C C A B" using equalanglessymmetric[OF `ang_eq C A B B A C`] .
	have "ang_eq B A C B D C" using equalanglestransitive[OF `ang_eq B A C C A B` `ang_eq C A B B D C`] .
	have "ang_eq B D C B A C" using equalanglessymmetric[OF `ang_eq B A C B D C`] .
	have "ang_right B D C" using equaltorightisright[OF `ang_right B A C` `ang_eq B D C B A C`] .
	have "ang_right C D B" using n8_2[OF `ang_right B D C`] .
	have "parallel A C B D" using parallelflip[OF `parallel A C D B`] by blast
	have "parallel A B C D" using parallelogram_f[OF `parallelogram A C D B`] by blast
	have "tarski_parallel A B C D" using paralleldef2B[OF `parallel A B C D`] .
	have "same_side C D A B" using tarski_parallel_f[OF `tarski_parallel A B C D`] by blast
	obtain E where "bet B A E \<and> seg_eq A E A B" using extensionE[OF `B \<noteq> A` `A \<noteq> B`]  by  blast
	have "bet B A E" using `bet B A E \<and> seg_eq A E A B` by blast
	have "bet E A B" using betweennesssymmetryE[OF `bet B A E`] .
	have "ang_sum_right C A B A B D" using Prop29C[OF `parallel A C B D` `same_side C D A B` `bet E A B`] by blast
	obtain p q r s t where "supplement p q r s t \<and> ang_eq C A B p q r \<and> ang_eq A B D s q t" using tworightangles_f[OF `ang_sum_right C A B A B D`]  by  blast
	have "supplement p q r s t" using `supplement p q r s t \<and> ang_eq C A B p q r \<and> ang_eq A B D s q t` by blast
	have "ang_eq C A B p q r" using `supplement p q r s t \<and> ang_eq C A B p q r \<and> ang_eq A B D s q t` by blast
	have "ang_eq A B D s q t" using `supplement p q r s t \<and> ang_eq C A B p q r \<and> ang_eq A B D s q t` by blast
	have "ang_eq p q r C A B" using equalanglessymmetric[OF `ang_eq C A B p q r`] .
	have "ang_right p q r" using equaltorightisright[OF `ang_right C A B` `ang_eq p q r C A B`] .
	have "ang_right s q t" using supplementofright[OF `supplement p q r s t` `ang_right p q r`] by blast
	have "ang_right A B D" using equaltorightisright[OF `ang_right s q t` `ang_eq A B D s q t`] .
	have "ang_right D B A" using n8_2[OF `ang_right A B D`] .
	have "ang_eq D C A A B D" using equalanglessymmetric[OF `ang_eq A B D D C A`] .
	have "ang_right D C A" using equaltorightisright[OF `ang_right A B D` `ang_eq D C A A B D`] .
	have "ang_right A C D" using n8_2[OF `ang_right D C A`] .
	obtain M where "bet A M D \<and> bet C M B" using diagonalsmeet[OF `parallelogram A C D B`]  by  blast
	have "bet A M D" using `bet A M D \<and> bet C M B` by blast
	have "bet C M B" using `bet A M D \<and> bet C M B` by blast
	have "cross A D C B" using cross_b[OF `bet A M D` `bet C M B`] .
	have "ang_right B A C \<and> ang_right A C D \<and> ang_right C D B \<and> ang_right D B A \<and> cross A D C B" using `ang_right B A C` `ang_right A C D` `ang_right C D B` `ang_right D B A` `cross A D C B` by blast
	have "rectangle A C D B" using rectangle_b[OF `ang_right B A C` `ang_right A C D` `ang_right C D B` `ang_right D B A` `cross A D C B`] .
	thus ?thesis by blast
qed

end