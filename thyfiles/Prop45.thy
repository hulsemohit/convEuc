theory Prop45
	imports n3_7b ABCequalsCBA Geometry NCdistinct NChelper NCorder Playfair Prop10 Prop14 Prop29C Prop30 Prop42B Prop44 RTcongruence RTsymmetric betweennotequal collinear4 collinearorder collinearparallel congruenceflip congruencesymmetric congruencetransitive diagonalsmeet equalanglesNC equalangleshelper equalanglesreflexive equalanglessymmetric equalanglestransitive inequalitysymmetric oppositesidesymmetric parallelNC paralleldef2B parallelflip parallelsymmetric planeseparation ray4 ray5 samesidecollinear samesidesymmetric
begin

theorem Prop45:
	assumes "axioms"
		"\<not> col J E N"
		"\<not> col A B D"
		"\<not> col C B D"
		"bet A pO C"
		"bet B pO D"
		"R \<noteq> K"
		"\<not> col K R S"
	shows "\<exists> F L M. parallelogram F K M L \<and> ang_eq F K M J E N \<and> qua_eq_area F K M L A B C D \<and> ray_on K R M \<and> same_side F S K M"
proof -
	have "B \<noteq> D" using NCdistinct[OF `axioms` `\<not> col A B D`] by blast
	obtain m where "bet B m D \<and> seg_eq m B m D" using Prop10[OF `axioms` `B \<noteq> D`]  by  blast
	have "bet B m D" using `bet B m D \<and> seg_eq m B m D` by blast
	have "seg_eq m B m D" using `bet B m D \<and> seg_eq m B m D` by blast
	have "seg_eq B m m D" using congruenceflip[OF `axioms` `seg_eq m B m D`] by blast
	have "midpoint B m D" using midpoint_b[OF `axioms` `bet B m D` `seg_eq B m m D`] .
	have "B \<noteq> m" using betweennotequal[OF `axioms` `bet B m D`] by blast
	obtain P where "bet R K P \<and> seg_eq K P B m" using extensionE[OF `axioms` `R \<noteq> K` `B \<noteq> m`]  by  blast
	have "bet R K P" using `bet R K P \<and> seg_eq K P B m` by blast
	have "seg_eq K P B m" using `bet R K P \<and> seg_eq K P B m` by blast
	have "triangle A B D" using triangle_b[OF `axioms` `\<not> col A B D`] .
	have "midpoint B m D" using `midpoint B m D` .
	have "\<not> col J E N" using `\<not> col J E N` .
	have "K \<noteq> P" using betweennotequal[OF `axioms` `bet R K P`] by blast
	have "P \<noteq> K" using inequalitysymmetric[OF `axioms` `K \<noteq> P`] .
	obtain H where "bet P K H \<and> seg_eq K H P K" using extensionE[OF `axioms` `P \<noteq> K` `P \<noteq> K`]  by  blast
	have "bet P K H" using `bet P K H \<and> seg_eq K H P K` by blast
	have "seg_eq K H P K" using `bet P K H \<and> seg_eq K H P K` by blast
	have "seg_eq P K K H" using congruencesymmetric[OF `axioms` `seg_eq K H P K`] .
	have "midpoint P K H" using midpoint_b[OF `axioms` `bet P K H` `seg_eq P K K H`] .
	have "seg_eq P K B m" using congruenceflip[OF `axioms` `seg_eq K P B m`] by blast
	have "seg_eq K H B m" using congruencetransitive[OF `axioms` `seg_eq K H P K` `seg_eq P K B m`] .
	have "seg_eq B m m D" using congruenceflip[OF `axioms` `seg_eq m B m D`] by blast
	have "seg_eq K H m D" using congruencetransitive[OF `axioms` `seg_eq K H B m` `seg_eq B m m D`] .
	have "bet P K R" using betweennesssymmetryE[OF `axioms` `bet R K P`] .
	have "col P K H" using collinear_b `axioms` `bet P K H \<and> seg_eq K H P K` by blast
	have "col P K R" using collinear_b `axioms` `bet P K R` by blast
	have "P \<noteq> K" using betweennotequal[OF `axioms` `bet P K H`] by blast
	have "col K H R" using collinear4[OF `axioms` `col P K H` `col P K R` `P \<noteq> K`] .
	have "col R K H" using collinearorder[OF `axioms` `col K H R`] by blast
	have "\<not> col R K S" using NCorder[OF `axioms` `\<not> col K R S`] by blast
	have "K = K" using equalityreflexiveE[OF `axioms`] .
	have "col R K K" using collinear_b `axioms` `K = K` by blast
	have "K \<noteq> H" using betweennotequal[OF `axioms` `bet P K H`] by blast
	have "H \<noteq> K" using inequalitysymmetric[OF `axioms` `K \<noteq> H`] .
	have "\<not> col H K S" using NChelper[OF `axioms` `\<not> col R K S` `col R K H` `col R K K` `H \<noteq> K`] .
	have "\<not> col S K H" using NCorder[OF `axioms` `\<not> col H K S`] by blast
	obtain F G where "parallelogram F K H G \<and> qua_eq_area A B m D F K H G \<and> ang_eq H K F J E N \<and> same_side S F K H" using Prop42B[OF `axioms` `triangle A B D` `midpoint B m D` `\<not> col J E N` `midpoint P K H` `seg_eq K H m D` `\<not> col S K H`]  by  blast
	have "parallelogram F K H G" using `parallelogram F K H G \<and> qua_eq_area A B m D F K H G \<and> ang_eq H K F J E N \<and> same_side S F K H` by blast
	have "\<not> col D B C" using NCorder[OF `axioms` `\<not> col C B D`] by blast
	have "triangle D B C" using triangle_b[OF `axioms` `\<not> col D B C`] .
	have "parallel F K H G" using parallelogram_f[OF `axioms` `parallelogram F K H G`] by blast
	have "\<not> col K H G" using parallelNC[OF `axioms` `parallel F K H G`] by blast
	have "\<not> col H G K" using NCorder[OF `axioms` `\<not> col K H G`] by blast
	have "\<not> col G H K" using NCorder[OF `axioms` `\<not> col H G K`] by blast
	obtain L M e where "parallelogram G H M L \<and> ang_eq G H M J E N \<and> qua_eq_area D B e C G H M L \<and> midpoint B e C \<and> oppo_side M G H K" using Prop44[OF `axioms` `triangle D B C` `\<not> col J E N` `\<not> col G H K`]  by  blast
	have "ang_eq G H M J E N" using `parallelogram G H M L \<and> ang_eq G H M J E N \<and> qua_eq_area D B e C G H M L \<and> midpoint B e C \<and> oppo_side M G H K` by blast
	have "midpoint B e C" using `parallelogram G H M L \<and> ang_eq G H M J E N \<and> qua_eq_area D B e C G H M L \<and> midpoint B e C \<and> oppo_side M G H K` by blast
	have "bet B e C" using midpoint_f[OF `axioms` `midpoint B e C`] by blast
	have "parallelogram F K H G" using `parallelogram F K H G` .
	have "parallelogram G H M L" using `parallelogram G H M L \<and> ang_eq G H M J E N \<and> qua_eq_area D B e C G H M L \<and> midpoint B e C \<and> oppo_side M G H K` by blast
	have "ang_eq H K F J E N" using `parallelogram F K H G \<and> qua_eq_area A B m D F K H G \<and> ang_eq H K F J E N \<and> same_side S F K H` by blast
	have "ang_eq J E N G H M" using equalanglessymmetric[OF `axioms` `ang_eq G H M J E N`] .
	have "ang_eq H K F G H M" using equalanglestransitive[OF `axioms` `ang_eq H K F J E N` `ang_eq J E N G H M`] .
	have "parallel F K H G" using parallelogram_f[OF `axioms` `parallelogram F K H G`] by blast
	have "parallel K F H G" using parallelflip[OF `axioms` `parallel F K H G`] by blast
	have "H \<noteq> K" using NCdistinct[OF `axioms` `\<not> col G H K`] by blast
	obtain s where "bet H K s \<and> seg_eq K s H K" using extensionE[OF `axioms` `H \<noteq> K` `H \<noteq> K`]  by  blast
	have "parallel F G K H" using parallelogram_f[OF `axioms` `parallelogram F K H G`] by blast
	have "parallel K H F G" using parallelsymmetric[OF `axioms` `parallel F G K H`] .
	have "tarski_parallel K H F G" using paralleldef2B[OF `axioms` `parallel K H F G`] .
	have "same_side F G K H" using tarski_parallel_f[OF `axioms` `tarski_parallel K H F G`] by blast
	have "ang_sum_right F K H K H G" using Prop29C[OF `axioms` `parallel K F H G` `same_side F G K H` `bet P K H`] by blast
	have "ang_eq G H M H K F" using equalanglessymmetric[OF `axioms` `ang_eq H K F G H M`] .
	have "\<not> col H K F" using equalanglesNC[OF `axioms` `ang_eq G H M H K F`] .
	have "\<not> col F K H" using NCorder[OF `axioms` `\<not> col H K F`] by blast
	have "ang_eq F K H H K F" using ABCequalsCBA[OF `axioms` `\<not> col F K H`] .
	have "ang_eq F K H G H M" using equalanglestransitive[OF `axioms` `ang_eq F K H H K F` `ang_eq H K F G H M`] .
	have "ang_sum_right G H M K H G" using RTcongruence[OF `axioms` `ang_sum_right F K H K H G` `ang_eq F K H G H M`] .
	have "ang_sum_right K H G G H M" using RTsymmetric[OF `axioms` `ang_sum_right G H M K H G`] .
	have "oppo_side M G H K" using `parallelogram G H M L \<and> ang_eq G H M J E N \<and> qua_eq_area D B e C G H M L \<and> midpoint B e C \<and> oppo_side M G H K` by blast
	have "G = G" using equalityreflexiveE[OF `axioms`] .
	have "H \<noteq> G" using NCdistinct[OF `axioms` `\<not> col G H K`] by blast
	have "ray_on H G G" using ray4 `axioms` `G = G` `H \<noteq> G` by blast
	have "ang_sum_right K H G G H M" using `ang_sum_right K H G G H M` .
	have "bet K H M" using Prop14[OF `axioms` `ang_sum_right K H G G H M` `ray_on H G G` `oppo_side M G H K`] by blast
	have "F \<noteq> K" using NCdistinct[OF `axioms` `\<not> col F K H`] by blast
	have "\<not> col G H M" using equalanglesNC[OF `axioms` `ang_eq F K H G H M`] .
	have "G \<noteq> H" using NCdistinct[OF `axioms` `\<not> col G H K`] by blast
	have "parallel G H M L" using parallelogram_f[OF `axioms` `parallelogram G H M L`] by blast
	have "\<not> col H M L" using parallelNC[OF `axioms` `parallel G H M L`] by blast
	have "L \<noteq> M" using NCdistinct[OF `axioms` `\<not> col H M L`] by blast
	have "K = K" using equalityreflexiveE[OF `axioms`] .
	have "H = H" using equalityreflexiveE[OF `axioms`] .
	have "M = M" using equalityreflexiveE[OF `axioms`] .
	have "col F K K" using collinear_b `axioms` `K = K` by blast
	have "col G H H" using collinear_b `axioms` `H = H` by blast
	have "col L M M" using collinear_b `axioms` `M = M` by blast
	have "bet K H M" using `bet K H M` .
	have "parallel F K G H" using parallelflip[OF `axioms` `parallel F K H G`] by blast
	have "parallel M L G H" using parallelsymmetric[OF `axioms` `parallel G H M L`] .
	have "parallel L M G H" using parallelflip[OF `axioms` `parallel M L G H`] by blast
	have "parallel F K L M" using Prop30[OF `axioms` `parallel F K G H` `parallel L M G H` `bet K H M` `col F K K` `col G H H` `col L M M` `F \<noteq> K` `G \<noteq> H` `L \<noteq> M`] .
	have "parallel F K M L" using parallelflip[OF `axioms` `parallel F K L M`] by blast
	have "parallelogram F K H G" using `parallelogram F K H G` .
	have "parallelogram G H M L" using `parallelogram G H M L` .
	have "parallel F G K H" using parallelogram_f[OF `axioms` `parallelogram F K H G`] by blast
	have "parallel G L H M" using parallelogram_f[OF `axioms` `parallelogram G H M L`] by blast
	have "parallel F G H K" using parallelflip[OF `axioms` `parallel F G K H`] by blast
	have "col K H M" using collinear_b `axioms` `bet K H M` by blast
	have "col H K M" using collinearorder[OF `axioms` `col K H M`] by blast
	have "K \<noteq> M" using betweennotequal[OF `axioms` `bet K H M`] by blast
	have "M \<noteq> K" using inequalitysymmetric[OF `axioms` `K \<noteq> M`] .
	have "parallel F G M K" using collinearparallel[OF `axioms` `parallel F G H K` `col H K M` `M \<noteq> K`] .
	have "col H M K" using collinearorder[OF `axioms` `col H K M`] by blast
	have "parallel G L K M" using collinearparallel[OF `axioms` `parallel G L H M` `col H M K` `K \<noteq> M`] .
	have "parallel G L M K" using parallelflip[OF `axioms` `parallel G L K M`] by blast
	have "parallel M K G L" using parallelsymmetric[OF `axioms` `parallel G L M K`] .
	have "parallel M K F G" using parallelsymmetric[OF `axioms` `parallel F G M K`] .
	have "parallel M K G F" using parallelflip[OF `axioms` `parallel M K F G`] by blast
	have "col G L F" using Playfair[OF `axioms` `parallel M K G L` `parallel M K G F`] .
	have "col G F L" using collinearorder[OF `axioms` `col G L F`] by blast
	have "\<not> col F L M" using parallelNC[OF `axioms` `parallel F K L M`] by blast
	have "L \<noteq> F" using NCdistinct[OF `axioms` `\<not> col F L M`] by blast
	have "parallel M K L F" using collinearparallel[OF `axioms` `parallel M K G F` `col G F L` `L \<noteq> F`] .
	have "parallel L F M K" using parallelsymmetric[OF `axioms` `parallel M K L F`] .
	have "parallel F L K M" using parallelflip[OF `axioms` `parallel L F M K`] by blast
	have "parallelogram F K M L" using parallelogram_b[OF `axioms` `parallel F K M L` `parallel F L K M`] .
	have "ang_eq H K F J E N" using `ang_eq H K F J E N` .
	have "\<not> col F K H" using parallelNC[OF `axioms` `parallel F G K H`] by blast
	have "ang_eq F K H H K F" using ABCequalsCBA[OF `axioms` `\<not> col F K H`] .
	have "ang_eq F K H J E N" using equalanglestransitive[OF `axioms` `ang_eq F K H G H M` `ang_eq G H M J E N`] .
	have "K \<noteq> H" using betweennotequal[OF `axioms` `bet K H M`] by blast
	have "ray_on K H M" using ray4 `axioms` `bet K H M` `K \<noteq> H` by blast
	have "ray_on K M H" using ray5[OF `axioms` `ray_on K H M`] .
	have "F = F" using equalityreflexiveE[OF `axioms`] .
	have "K \<noteq> F" using NCdistinct[OF `axioms` `\<not> col F K H`] by blast
	have "ray_on K F F" using ray4 `axioms` `F = F` `K \<noteq> F` by blast
	have "\<not> col F K M" using parallelNC[OF `axioms` `parallel F K L M`] by blast
	have "ang_eq F K M F K M" using equalanglesreflexive[OF `axioms` `\<not> col F K M`] .
	have "ang_eq F K M F K H" using equalangleshelper[OF `axioms` `ang_eq F K M F K M` `ray_on K F F` `ray_on K M H`] .
	have "ang_eq F K M J E N" using equalanglestransitive[OF `axioms` `ang_eq F K M F K H` `ang_eq F K H J E N`] .
	have "qua_eq_area A B m D F K H G" using `parallelogram F K H G \<and> qua_eq_area A B m D F K H G \<and> ang_eq H K F J E N \<and> same_side S F K H` by blast
	have "qua_eq_area D B e C G H M L" using `parallelogram G H M L \<and> ang_eq G H M J E N \<and> qua_eq_area D B e C G H M L \<and> midpoint B e C \<and> oppo_side M G H K` by blast
	have "col B pO D" using collinear_b `axioms` `bet B pO D` by blast
	have "col B D pO" using collinearorder[OF `axioms` `col B pO D`] by blast
	have "\<not> col B D A" using NCorder[OF `axioms` `\<not> col A B D`] by blast
	have "oppo_side A B D C" using oppositeside_b[OF `axioms` `bet A pO C` `col B D pO` `\<not> col B D A`] .
	have "bet K H M" using `bet K H M` .
	have "parallel G H L M" using parallelflip[OF `axioms` `parallel G H M L`] by blast
	have "tarski_parallel G H L M" using paralleldef2B[OF `axioms` `parallel G H L M`] .
	have "same_side L M G H" using tarski_parallel_f[OF `axioms` `tarski_parallel G H L M`] by blast
	have "parallel F K G H" using parallelflip[OF `axioms` `parallel F K H G`] by blast
	have "parallel G H F K" using parallelsymmetric[OF `axioms` `parallel F K G H`] .
	have "tarski_parallel G H F K" using paralleldef2B[OF `axioms` `parallel G H F K`] .
	have "same_side F K G H" using tarski_parallel_f[OF `axioms` `tarski_parallel G H F K`] by blast
	have "H = H" using equalityreflexiveE[OF `axioms`] .
	have "col G H H" using collinear_b `axioms` `H = H` by blast
	have "oppo_side K G H M" using oppositeside_b[OF `axioms` `bet K H M` `col G H H` `\<not> col G H K`] .
	have "oppo_side F G H M" using planeseparation[OF `axioms` `same_side F K G H` `oppo_side K G H M`] .
	have "oppo_side M G H F" using oppositesidesymmetric[OF `axioms` `oppo_side F G H M`] .
	have "oppo_side L G H F" using planeseparation[OF `axioms` `same_side L M G H` `oppo_side M G H F`] .
	obtain t where "bet L t F \<and> col G H t \<and> \<not> col G H L" using oppositeside_f[OF `axioms` `oppo_side L G H F`]  by  blast
	have "bet L t F" using `bet L t F \<and> col G H t \<and> \<not> col G H L` by blast
	have "col G H t" using `bet L t F \<and> col G H t \<and> \<not> col G H L` by blast
	have "col F L G" using collinearorder[OF `axioms` `col G F L`] by blast
	have "col L t F" using collinear_b `axioms` `bet L t F \<and> col G H t \<and> \<not> col G H L` by blast
	have "col F L t" using collinearorder[OF `axioms` `col L t F`] by blast
	have "F \<noteq> L" using NCdistinct[OF `axioms` `\<not> col F L M`] by blast
	have "col L G t" using collinear4[OF `axioms` `col F L G` `col F L t` `F \<noteq> L`] .
	have "col t G L" using collinearorder[OF `axioms` `col L G t`] by blast
	have "col t G H" using collinearorder[OF `axioms` `col G H t`] by blast
	have "\<not> (t \<noteq> G)"
	proof (rule ccontr)
		assume "\<not> (\<not> (t \<noteq> G))"
hence "t \<noteq> G" by blast
		have "col G L H" using collinear4[OF `axioms` `col t G L` `col t G H` `t \<noteq> G`] .
		have "col G H L" using collinearorder[OF `axioms` `col G L H`] by blast
		have "\<not> col G H L" using `bet L t F \<and> col G H t \<and> \<not> col G H L` by blast
		show "False" using `\<not> col G H L` `col G H L` by blast
	qed
	hence "t = G" by blast
	have "bet L G F" using `bet L t F` `t = G` by blast
	have "bet F G L" using betweennesssymmetryE[OF `axioms` `bet L G F`] .
	have "parallelogram F K M L" using `parallelogram F K M L` .
	obtain j where "bet F j M \<and> bet K j L" using diagonalsmeet[OF `axioms` `parallelogram F K M L`]  by  blast
	have "bet F j M" using `bet F j M \<and> bet K j L` by blast
	have "bet K j L" using `bet F j M \<and> bet K j L` by blast
	have "qua_eq_area A B C D F K M L" using paste4E[OF `axioms` `qua_eq_area A B m D F K H G` `qua_eq_area D B e C G H M L` `bet A pO C` `bet B pO D` `bet K H M` `bet F G L` `bet B m D` `bet B e C` `bet F j M` `bet K j L`] .
	have "qua_eq_area F K M L A B C D" using EFsymmetricE[OF `axioms` `qua_eq_area A B C D F K M L`] .
	have "bet P K H" using `bet P K H` .
	have "bet K H M" using `bet K H M` .
	have "bet P K R" using `bet P K R` .
	have "bet P K M" using n3_7b[OF `axioms` `bet P K H` `bet K H M`] .
	have "bet P K M \<and> bet P K R" using `bet P K M` `bet P K R` by blast
	have "ray_on K R M" using ray_b[OF `axioms` `bet P K M` `bet P K R`] .
	have "same_side S F K H" using `parallelogram F K H G \<and> qua_eq_area A B m D F K H G \<and> ang_eq H K F J E N \<and> same_side S F K H` by blast
	have "same_side F S K H" using samesidesymmetric[OF `axioms` `same_side S F K H`] by blast
	have "col K H M" using collinear_b `axioms` `bet K H M` by blast
	have "same_side F S K M" using samesidecollinear[OF `axioms` `same_side F S K H` `col K H M` `K \<noteq> M`] .
	have "parallelogram F K M L \<and> ang_eq F K M J E N \<and> qua_eq_area F K M L A B C D \<and> ray_on K R M \<and> same_side F S K M" using `parallelogram F K M L` `ang_eq F K M J E N` `qua_eq_area F K M L A B C D` `ray_on K R M` `same_side F S K M` by blast
	thus ?thesis by blast
qed

end