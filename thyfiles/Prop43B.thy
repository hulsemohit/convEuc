theory Prop43B
	imports n3_6a Geometry NCorder Prop28D Prop29C betweennotequal collinearorder collinearparallel equalanglesflip equalangleshelper equalanglesreflexive equalanglessymmetric inequalitysymmetric parallelNC paralleldef2B parallelflip parallelsymmetric ray4 ray5 sameside2 samesidecollinear samesideflip samesidesymmetric samesidetransitive supplements2
begin

theorem Prop43B:
	assumes "axioms"
		"parallelogram A B C D"
		"bet A H D"
		"bet A E B"
		"bet D F C"
		"bet B G C"
		"parallelogram E A H K"
		"parallelogram G K F C"
	shows "parallelogram E K G B"
proof -
	have "parallel A D B C" using parallelogram_f[OF `axioms` `parallelogram A B C D`] by blast
	have "parallel A B C D" using parallelogram_f[OF `axioms` `parallelogram A B C D`] by blast
	have "parallel E A H K" using parallelogram_f[OF `axioms` `parallelogram E A H K`] by blast
	have "parallel E K A H" using parallelogram_f[OF `axioms` `parallelogram E A H K`] by blast
	have "parallel G K F C" using parallelogram_f[OF `axioms` `parallelogram G K F C`] by blast
	have "parallel F C G K" using parallelsymmetric[OF `axioms` `parallel G K F C`] .
	have "parallel C F G K" using parallelflip[OF `axioms` `parallel F C G K`] by blast
	have "parallel G C K F" using parallelogram_f[OF `axioms` `parallelogram G K F C`] by blast
	have "parallel B C A D" using parallelsymmetric[OF `axioms` `parallel A D B C`] .
	have "parallel C D A B" using parallelsymmetric[OF `axioms` `parallel A B C D`] .
	have "parallel A H E K" using parallelsymmetric[OF `axioms` `parallel E K A H`] .
	have "tarski_parallel A B C D" using paralleldef2B[OF `axioms` `parallel A B C D`] .
	have "tarski_parallel E A H K" using paralleldef2B[OF `axioms` `parallel E A H K`] .
	have "tarski_parallel G C K F" using paralleldef2B[OF `axioms` `parallel G C K F`] .
	have "tarski_parallel B C A D" using paralleldef2B[OF `axioms` `parallel B C A D`] .
	have "same_side A D B C" using tarski_parallel_f[OF `axioms` `tarski_parallel B C A D`] by blast
	have "same_side A D C B" using samesideflip[OF `axioms` `same_side A D B C`] .
	have "same_side D A C B" using samesidesymmetric[OF `axioms` `same_side A D B C`] by blast
	have "same_side C D A B" using tarski_parallel_f[OF `axioms` `tarski_parallel A B C D`] by blast
	have "same_side H K E A" using tarski_parallel_f[OF `axioms` `tarski_parallel E A H K`] by blast
	have "same_side K F G C" using tarski_parallel_f[OF `axioms` `tarski_parallel G C K F`] by blast
	have "A \<noteq> E" using betweennotequal[OF `axioms` `bet A E B`] by blast
	have "A \<noteq> H" using betweennotequal[OF `axioms` `bet A H D`] by blast
	have "B \<noteq> G" using betweennotequal[OF `axioms` `bet B G C`] by blast
	have "A \<noteq> B" using betweennotequal[OF `axioms` `bet A E B`] by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
	obtain e where "bet B A e \<and> seg_eq A e B A" using extensionE[OF `axioms` `B \<noteq> A` `B \<noteq> A`]  by  blast
	have "bet B A e" using `bet B A e \<and> seg_eq A e B A` by blast
	have "bet e A B" using betweennesssymmetryE[OF `axioms` `bet B A e`] .
	have "same_side D C A B" using samesidesymmetric[OF `axioms` `same_side C D A B`] by blast
	have "parallel A D B C" using `parallel A D B C` .
	have "ang_sum_right D A B A B C" using Prop29C[OF `axioms` `parallel A D B C` `same_side D C A B` `bet e A B`] by blast
	have "bet B E A" using betweennesssymmetryE[OF `axioms` `bet A E B`] .
	have "bet E A e" using n3_6a[OF `axioms` `bet B E A` `bet B A e`] .
	have "bet e A E" using betweennesssymmetryE[OF `axioms` `bet E A e`] .
	have "parallel A H E K" using `parallel A H E K` .
	have "same_side H K A E" using samesidesymmetric[OF `axioms` `same_side H K E A`] by blast
	have "ang_sum_right H A E A E K" using Prop29C[OF `axioms` `parallel A H E K` `same_side H K A E` `bet e A E`] by blast
	have "ray_on A E B" using ray4 `axioms` `bet A E B` `A \<noteq> E` by blast
	have "ray_on A H D" using ray4 `axioms` `bet A H D` `A \<noteq> H` by blast
	have "\<not> col A H E" using parallelNC[OF `axioms` `parallel A H E K`] by blast
	have "\<not> col E A H" using NCorder[OF `axioms` `\<not> col A H E`] by blast
	have "ang_eq E A H E A H" using equalanglesreflexive[OF `axioms` `\<not> col E A H`] .
	have "ang_eq E A H B A D" using equalangleshelper[OF `axioms` `ang_eq E A H E A H` `ray_on A E B` `ray_on A H D`] .
	have "ang_eq H A E D A B" using equalanglesflip[OF `axioms` `ang_eq E A H B A D`] .
	have "ang_eq A E K A B C" using supplements2[OF `axioms` `ang_sum_right H A E A E K` `ang_eq H A E D A B` `ang_sum_right D A B A B C`] by blast
	have "same_side C D A B" using `same_side C D A B` .
	have "same_side C D B A" using samesideflip[OF `axioms` `same_side C D A B`] .
	have "col A E B" using collinear_b `axioms` `bet A E B` by blast
	have "col B A E" using collinearorder[OF `axioms` `col A E B`] by blast
	have "E \<noteq> B" using betweennotequal[OF `axioms` `bet A E B`] by blast
	have "B \<noteq> E" using inequalitysymmetric[OF `axioms` `E \<noteq> B`] .
	have "same_side C D B E" using samesidecollinear[OF `axioms` `same_side C D B A` `col B A E` `B \<noteq> E`] .
	have "ray_on A H D" using ray4 `axioms` `bet A H D` `A \<noteq> H` by blast
	have "ray_on A D H" using ray5[OF `axioms` `ray_on A H D`] .
	have "same_side C H B E" using sameside2[OF `axioms` `same_side C D B E` `col B A E` `ray_on A D H`] .
	have "same_side H K E A" using `same_side H K E A` .
	have "col E A B" using collinearorder[OF `axioms` `col A E B`] by blast
	have "same_side H K E B" using samesidecollinear[OF `axioms` `same_side H K E A` `col E A B` `E \<noteq> B`] .
	have "same_side H K B E" using samesideflip[OF `axioms` `same_side H K E B`] .
	have "same_side C K B E" using samesidetransitive[OF `axioms` `same_side C H B E` `same_side H K B E`] .
	have "same_side K C B E" using samesidesymmetric[OF `axioms` `same_side C K B E`] by blast
	have "ray_on B G C" using ray4 `axioms` `bet B G C` `B \<noteq> G` by blast
	have "ray_on B C G" using ray5[OF `axioms` `ray_on B G C`] .
	have "B = B" using equalityreflexiveE[OF `axioms`] .
	have "col B B E" using collinear_b `axioms` `B = B` by blast
	have "same_side K G B E" using sameside2[OF `axioms` `same_side K C B E` `col B B E` `ray_on B C G`] .
	have "same_side K G E B" using samesideflip[OF `axioms` `same_side K G B E`] .
	have "ray_on B E A" using ray4 `axioms` `bet B E A` `B \<noteq> E` by blast
	have "ray_on B A E" using ray5[OF `axioms` `ray_on B E A`] .
	have "ang_eq A E K E B G" using equalangleshelper[OF `axioms` `ang_eq A E K A B C` `ray_on B A E` `ray_on B C G`] .
	have "parallel E K B G" using Prop28D[OF `axioms` `bet A E B` `ang_eq A E K E B G` `same_side K G E B`] .
	have "parallel E K G B" using parallelflip[OF `axioms` `parallel E K B G`] by blast
	have "same_side D A C B" using `same_side D A C B` .
	have "B \<noteq> C" using betweennotequal[OF `axioms` `bet B G C`] by blast
	obtain c where "bet B C c \<and> seg_eq C c B C" using extensionE[OF `axioms` `B \<noteq> C` `B \<noteq> C`]  by  blast
	have "bet B C c" using `bet B C c \<and> seg_eq C c B C` by blast
	have "bet c C B" using betweennesssymmetryE[OF `axioms` `bet B C c`] .
	have "parallel C D B A" using parallelflip[OF `axioms` `parallel C D A B`] by blast
	have "ang_sum_right D C B C B A" using Prop29C[OF `axioms` `parallel C D B A` `same_side D A C B` `bet c C B`] by blast
	have "parallel C F G K" using `parallel C F G K` .
	have "same_side K F G C" using `same_side K F G C` .
	have "same_side K F C G" using samesideflip[OF `axioms` `same_side K F G C`] .
	have "same_side F K C G" using samesidesymmetric[OF `axioms` `same_side K F C G`] by blast
	have "bet C G B" using betweennesssymmetryE[OF `axioms` `bet B G C`] .
	have "bet c C G" using innertransitivityE[OF `axioms` `bet c C B` `bet C G B`] .
	have "ang_sum_right F C G C G K" using Prop29C[OF `axioms` `parallel C F G K` `same_side F K C G` `bet c C G`] by blast
	have "\<not> col D B C" using parallelNC[OF `axioms` `parallel A D B C`] by blast
	have "\<not> col D C B" using NCorder[OF `axioms` `\<not> col D B C`] by blast
	have "ang_eq D C B D C B" using equalanglesreflexive[OF `axioms` `\<not> col D C B`] .
	have "bet C F D" using betweennesssymmetryE[OF `axioms` `bet D F C`] .
	have "C \<noteq> F" using betweennotequal[OF `axioms` `bet C F D`] by blast
	have "ray_on C F D" using ray4 `axioms` `bet C F D` `C \<noteq> F` by blast
	have "ray_on C D F" using ray5[OF `axioms` `ray_on C F D`] .
	have "bet C G B" using betweennesssymmetryE[OF `axioms` `bet B G C`] .
	have "C \<noteq> G" using betweennotequal[OF `axioms` `bet C G B`] by blast
	have "ray_on C G B" using ray4 `axioms` `bet C G B` `C \<noteq> G` by blast
	have "ray_on C B G" using ray5[OF `axioms` `ray_on C G B`] .
	have "ang_eq D C B F C G" using equalangleshelper[OF `axioms` `ang_eq D C B D C B` `ray_on C D F` `ray_on C B G`] .
	have "ang_eq C B A C G K" using supplements2[OF `axioms` `ang_sum_right D C B C B A` `ang_eq D C B F C G` `ang_sum_right F C G C G K`] by blast
	have "ang_eq C G K C B A" using equalanglessymmetric[OF `axioms` `ang_eq C B A C G K`] .
	have "A = A" using equalityreflexiveE[OF `axioms`] .
	have "ray_on B A A" using ray4 `axioms` `A = A` `B \<noteq> A` by blast
	have "B \<noteq> G" using betweennotequal[OF `axioms` `bet B G C`] by blast
	have "ray_on B G C" using ray4 `axioms` `bet B G C` `B \<noteq> G` by blast
	have "ray_on B C G" using ray5[OF `axioms` `ray_on B G C`] .
	have "ang_eq C G K G B A" using equalangleshelper[OF `axioms` `ang_eq C G K C B A` `ray_on B C G` `ray_on B A A`] .
	have "col B G C" using collinear_b `axioms` `bet B G C` by blast
	have "col C B G" using collinearorder[OF `axioms` `col B G C`] by blast
	have "same_side A D B C" using `same_side A D B C` .
	have "bet C F D" using betweennesssymmetryE[OF `axioms` `bet D F C`] .
	have "C \<noteq> F" using betweennotequal[OF `axioms` `bet C F D`] by blast
	have "ray_on C F D" using ray4 `axioms` `bet C F D` `C \<noteq> F` by blast
	have "ray_on C D F" using ray5[OF `axioms` `ray_on C F D`] .
	have "C = C" using equalityreflexiveE[OF `axioms`] .
	have "col B C C" using collinear_b `axioms` `C = C` by blast
	have "same_side A F B C" using sameside2[OF `axioms` `same_side A D B C` `col B C C` `ray_on C D F`] .
	have "parallel G C K F" using `parallel G C K F` .
	have "tarski_parallel G C K F" using paralleldef2B[OF `axioms` `parallel G C K F`] .
	have "same_side K F G C" using tarski_parallel_f[OF `axioms` `tarski_parallel G C K F`] by blast
	have "col C G B" using collinearorder[OF `axioms` `col B G C`] by blast
	have "C \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> C`] .
	have "same_side K F C G" using samesideflip[OF `axioms` `same_side K F G C`] .
	have "same_side K F C B" using samesidecollinear[OF `axioms` `same_side K F C G` `col C G B` `C \<noteq> B`] .
	have "same_side K F B C" using samesideflip[OF `axioms` `same_side K F C B`] .
	have "same_side F K B C" using samesidesymmetric[OF `axioms` `same_side K F B C`] by blast
	have "same_side A K B C" using samesidetransitive[OF `axioms` `same_side A F B C` `same_side F K B C`] .
	have "same_side K A B C" using samesidesymmetric[OF `axioms` `same_side A K B C`] by blast
	have "col B C G" using collinearorder[OF `axioms` `col B G C`] by blast
	have "B \<noteq> G" using `B \<noteq> G` .
	have "same_side K A B G" using samesidecollinear[OF `axioms` `same_side K A B C` `col B C G` `B \<noteq> G`] .
	have "same_side K A G B" using samesideflip[OF `axioms` `same_side K A B G`] .
	have "parallel G K B A" using Prop28D[OF `axioms` `bet C G B` `ang_eq C G K G B A` `same_side K A G B`] .
	have "parallel G K A B" using parallelflip[OF `axioms` `parallel G K B A`] by blast
	have "col A B E" using collinearorder[OF `axioms` `col A E B`] by blast
	have "parallel G K E B" using collinearparallel[OF `axioms` `parallel G K A B` `col A B E` `E \<noteq> B`] .
	have "parallel E B G K" using parallelsymmetric[OF `axioms` `parallel G K E B`] .
	have "parallel E B K G" using parallelflip[OF `axioms` `parallel E B G K`] by blast
	have "parallelogram E K G B" using parallelogram_b[OF `axioms` `parallel E K G B` `parallel E B K G`] .
	thus ?thesis by blast
qed

end