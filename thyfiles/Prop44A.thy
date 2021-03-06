theory Prop44A
	imports ABCequalsCBA Geometry NCdistinct NChelper NCorder PGflip PGrotate Playfair Prop15 Prop30 Prop31 Prop33B Prop34 Prop43 Prop43B betweennotequal collinearbetween collinearorder collinearparallel collinearparallel2 congruenceflip congruencetransitive diagonalsbisect diagonalsmeet equalanglestransitive inequalitysymmetric parallelNC parallelbetween paralleldef2B parallelflip parallelsymmetric samesidecollinear samesideflip samesidetransitive triangletoparallelogram
begin

theorem(in euclidean_geometry) Prop44A:
	assumes 
		"parallelogram B E F G"
		"ang_eq E B G J D N"
		"bet A B E"
	shows "\<exists> L M. parallelogram A B M L \<and> ang_eq A B M J D N \<and> qua_eq_area B E F G L M B A \<and> bet G B M"
proof -
	have "parallelogram E F G B" using PGrotate[OF `parallelogram B E F G`] .
	have "parallelogram F G B E" using PGrotate[OF `parallelogram E F G B`] .
	have "parallelogram G B E F" using PGrotate[OF `parallelogram F G B E`] .
	have "parallel G F B E" using parallelogram_f[OF `parallelogram G B E F`] by blast
	have "\<not> col G B E" using parallelNC[OF `parallel G F B E`] by blast
	have "G \<noteq> B" using NCdistinct[OF `\<not> col G B E`] by blast
	obtain q where "bet G B q \<and> seg_eq B q G B" using extensionE[OF `G \<noteq> B` `G \<noteq> B`]  by  blast
	have "bet G B q" using `bet G B q \<and> seg_eq B q G B` by blast
	have "seg_eq B q G B" using `bet G B q \<and> seg_eq B q G B` by blast
	have "\<not> col E B G" using NCorder[OF `\<not> col G B E`] by blast
	have "col A B E" using collinear_b `bet A B E` by blast
	have "col E B A" using collinearorder[OF `col A B E`] by blast
	have "B = B" using equalityreflexiveE.
	have "col E B B" using collinear_b `B = B` by blast
	have "A \<noteq> B" using betweennotequal[OF `bet A B E`] by blast
	have "\<not> col A B G" using NChelper[OF `\<not> col E B G` `col E B A` `col E B B` `A \<noteq> B`] .
	have "col G B q" using collinear_b `bet G B q \<and> seg_eq B q G B` by blast
	have "\<not> col G B A" using NCorder[OF `\<not> col A B G`] by blast
	have "G \<noteq> q" using betweennotequal[OF `bet G B q`] by blast
	have "q \<noteq> G" using inequalitysymmetric[OF `G \<noteq> q`] .
	have "G = G" using equalityreflexiveE.
	have "col G B G" using collinear_b `G = G` by blast
	have "\<not> col q G A" using NChelper[OF `\<not> col G B A` `col G B q` `col G B G` `q \<noteq> G`] .
	have "\<not> col G q A" using NCorder[OF `\<not> col q G A`] by blast
	obtain H T h where "bet H A h \<and> ang_eq h A B A B G \<and> ang_eq h A B G B A \<and> ang_eq B A h G B A \<and> ang_eq H A B A B q \<and> ang_eq H A B q B A \<and> ang_eq B A H q B A \<and> parallel H h G q \<and> seg_eq H A B q \<and> seg_eq A h G B \<and> seg_eq A T T B \<and> seg_eq H T T q \<and> seg_eq G T T h \<and> bet H T q \<and> bet G T h \<and> bet A T B" using Prop31[OF `bet G B q` `\<not> col G q A`]  by  blast
	have "bet H A h" using `bet H A h \<and> ang_eq h A B A B G \<and> ang_eq h A B G B A \<and> ang_eq B A h G B A \<and> ang_eq H A B A B q \<and> ang_eq H A B q B A \<and> ang_eq B A H q B A \<and> parallel H h G q \<and> seg_eq H A B q \<and> seg_eq A h G B \<and> seg_eq A T T B \<and> seg_eq H T T q \<and> seg_eq G T T h \<and> bet H T q \<and> bet G T h \<and> bet A T B` by blast
	have "parallel H h G q" using `bet H A h \<and> ang_eq h A B A B G \<and> ang_eq h A B G B A \<and> ang_eq B A h G B A \<and> ang_eq H A B A B q \<and> ang_eq H A B q B A \<and> ang_eq B A H q B A \<and> parallel H h G q \<and> seg_eq H A B q \<and> seg_eq A h G B \<and> seg_eq A T T B \<and> seg_eq H T T q \<and> seg_eq G T T h \<and> bet H T q \<and> bet G T h \<and> bet A T B` by blast
	have "bet H T q" using `bet H A h \<and> ang_eq h A B A B G \<and> ang_eq h A B G B A \<and> ang_eq B A h G B A \<and> ang_eq H A B A B q \<and> ang_eq H A B q B A \<and> ang_eq B A H q B A \<and> parallel H h G q \<and> seg_eq H A B q \<and> seg_eq A h G B \<and> seg_eq A T T B \<and> seg_eq H T T q \<and> seg_eq G T T h \<and> bet H T q \<and> bet G T h \<and> bet A T B` by blast
	have "bet A T B" using `bet H A h \<and> ang_eq h A B A B G \<and> ang_eq h A B G B A \<and> ang_eq B A h G B A \<and> ang_eq H A B A B q \<and> ang_eq H A B q B A \<and> ang_eq B A H q B A \<and> parallel H h G q \<and> seg_eq H A B q \<and> seg_eq A h G B \<and> seg_eq A T T B \<and> seg_eq H T T q \<and> seg_eq G T T h \<and> bet H T q \<and> bet G T h \<and> bet A T B` by blast
	have "seg_eq H A B q" using `bet H A h \<and> ang_eq h A B A B G \<and> ang_eq h A B G B A \<and> ang_eq B A h G B A \<and> ang_eq H A B A B q \<and> ang_eq H A B q B A \<and> ang_eq B A H q B A \<and> parallel H h G q \<and> seg_eq H A B q \<and> seg_eq A h G B \<and> seg_eq A T T B \<and> seg_eq H T T q \<and> seg_eq G T T h \<and> bet H T q \<and> bet G T h \<and> bet A T B` by blast
	have "parallel H h q G" using parallelflip[OF `parallel H h G q`] by blast
	have "col G B q" using collinear_b `bet G B q \<and> seg_eq B q G B` by blast
	have "col q G B" using collinearorder[OF `col G B q`] by blast
	have "B \<noteq> G" using NCdistinct[OF `\<not> col A B G`] by blast
	have "parallel H h B G" using collinearparallel[OF `parallel H h q G` `col q G B` `B \<noteq> G`] .
	have "parallel H h G B" using parallelflip[OF `parallel H h B G`] by blast
	have "parallel G B H h" using parallelsymmetric[OF `parallel H h G B`] .
	have "parallel G B h H" using parallelflip[OF `parallel G B H h`] by blast
	have "col H A h" using collinear_b `bet H A h \<and> ang_eq h A B A B G \<and> ang_eq h A B G B A \<and> ang_eq B A h G B A \<and> ang_eq H A B A B q \<and> ang_eq H A B q B A \<and> ang_eq B A H q B A \<and> parallel H h G q \<and> seg_eq H A B q \<and> seg_eq A h G B \<and> seg_eq A T T B \<and> seg_eq H T T q \<and> seg_eq G T T h \<and> bet H T q \<and> bet G T h \<and> bet A T B` by blast
	have "col h H A" using collinearorder[OF `col H A h`] by blast
	have "H \<noteq> A" using betweennotequal[OF `bet H A h`] by blast
	have "A \<noteq> H" using inequalitysymmetric[OF `H \<noteq> A`] .
	have "parallel G B A H" using collinearparallel[OF `parallel G B h H` `col h H A` `A \<noteq> H`] .
	have "parallel G B H A" using parallelflip[OF `parallel G B A H`] by blast
	have "parallel H A G B" using parallelsymmetric[OF `parallel G B H A`] .
	have "seg_eq H A G B" using congruencetransitive[OF `seg_eq H A B q` `seg_eq B q G B`] .
	have "B = B" using equalityreflexiveE.
	have "col A B B" using collinear_b `B = B` by blast
	have "col A T B" using collinear_b `bet H A h \<and> ang_eq h A B A B G \<and> ang_eq h A B G B A \<and> ang_eq B A h G B A \<and> ang_eq H A B A B q \<and> ang_eq H A B q B A \<and> ang_eq B A H q B A \<and> parallel H h G q \<and> seg_eq H A B q \<and> seg_eq A h G B \<and> seg_eq A T T B \<and> seg_eq H T T q \<and> seg_eq G T T h \<and> bet H T q \<and> bet G T h \<and> bet A T B` by blast
	have "col A B T" using collinearorder[OF `col A T B`] by blast
	have "\<not> col B H A" using parallelNC[OF `parallel G B H A`] by blast
	have "\<not> col A B H" using NCorder[OF `\<not> col B H A`] by blast
	have "\<not> col H A B" using parallelNC[OF `parallel H A G B`] by blast
	have "\<not> col A B H" using NCorder[OF `\<not> col B H A`] by blast
	have "col A B T \<and> col A B B \<and> bet H T q \<and> bet G B q \<and> \<not> col A B H \<and> \<not> col A B G" using `col A B T` `col A B B` `bet H A h \<and> ang_eq h A B A B G \<and> ang_eq h A B G B A \<and> ang_eq B A h G B A \<and> ang_eq H A B A B q \<and> ang_eq H A B q B A \<and> ang_eq B A H q B A \<and> parallel H h G q \<and> seg_eq H A B q \<and> seg_eq A h G B \<and> seg_eq A T T B \<and> seg_eq H T T q \<and> seg_eq G T T h \<and> bet H T q \<and> bet G T h \<and> bet A T B` `bet G B q \<and> seg_eq B q G B` `\<not> col A B H` `\<not> col A B G` by blast
	have "same_side H G A B" using sameside_b[OF `col A B T` `col A B B` `bet H T q` `bet G B q` `\<not> col A B H` `\<not> col A B G`] .
	have "parallel H G A B \<and> seg_eq H G A B" using Prop33B[OF `parallel H A G B` `seg_eq H A G B` `same_side H G A B`] .
	have "parallel H G A B" using `parallel H G A B \<and> seg_eq H G A B` by blast
	have "parallel A B H G" using parallelsymmetric[OF `parallel H G A B`] .
	have "parallel A B G H" using parallelflip[OF `parallel A B H G`] by blast
	have "parallelogram G B E F" using `parallelogram G B E F` .
	have "parallel G B E F \<and> parallel G F B E" using parallelogram_f[OF `parallelogram G B E F`] .
	have "parallel G B E F" using `parallel G B E F \<and> parallel G F B E` by blast
	have "parallel G F B E" using `parallel G F B E` .
	have "parallel G F E B" using parallelflip[OF `parallel G F B E`] by blast
	have "col A B E" using collinear_b `bet A B E` by blast
	have "col E B A" using collinearorder[OF `col A B E`] by blast
	have "parallel G F A B" using collinearparallel[OF `parallel G F E B` `col E B A` `A \<noteq> B`] .
	have "parallel A B G F" using parallelsymmetric[OF `parallel G F A B`] .
	have "col G H F" using Playfair[OF `parallel A B G H` `parallel A B G F`] .
	have "parallel H A B G" using parallelflip[OF `parallel H A G B`] by blast
	have "parallel G B F E" using parallelflip[OF `parallel G B E F`] by blast
	have "parallel F E G B" using parallelsymmetric[OF `parallel G B F E`] .
	have "parallelogram H A B G" using parallelogram_b[OF `parallel H A B G` `parallel H G A B`] .
	obtain j where "bet H j B \<and> bet A j G" using diagonalsmeet[OF `parallelogram H A B G`]  by  blast
	have "bet H j B" using `bet H j B \<and> bet A j G` by blast
	have "bet A j G" using `bet H j B \<and> bet A j G` by blast
	have "parallelogram G B E F" using `parallelogram G B E F` .
	obtain k where "bet G k E \<and> bet B k F" using diagonalsmeet[OF `parallelogram G B E F`]  by  blast
	have "bet G k E" using `bet G k E \<and> bet B k F` by blast
	have "bet B k F" using `bet G k E \<and> bet B k F` by blast
	have "parallel H A G B" using `parallel H A G B` .
	have "parallel F E G B" using `parallel F E G B` .
	have "bet E B A" using betweennesssymmetryE[OF `bet A B E`] .
	have "E = E" using equalityreflexiveE.
	have "B = B" using equalityreflexiveE.
	have "A = A" using equalityreflexiveE.
	have "col F E E" using collinear_b `E = E` by blast
	have "col G B B" using collinear_b `B = B` by blast
	have "col H A A" using collinear_b `A = A` by blast
	have "\<not> col F E B" using parallelNC[OF `parallel F E G B`] by blast
	have "F \<noteq> E" using NCdistinct[OF `\<not> col F E B`] by blast
	have "G \<noteq> B" using NCdistinct[OF `\<not> col A B G`] by blast
	have "\<not> col H A G" using parallelNC[OF `parallel H A B G`] by blast
	have "H \<noteq> A" using NCdistinct[OF `\<not> col A B H`] by blast
	have "parallel H A F E" using Prop30[OF `parallel H A G B` `parallel F E G B` `bet A B E` `col H A A` `col G B B` `col F E E` `H \<noteq> A` `G \<noteq> B` `F \<noteq> E`] .
	have "seg_eq H A G B" using `seg_eq H A G B` .
	have "seg_eq G B F E" using Prop34[OF `parallelogram G B E F`] by blast
	have "seg_eq H A F E" using congruencetransitive[OF `seg_eq H A G B` `seg_eq G B F E`] .
	have "parallelogram H A B G" using `parallelogram H A B G` .
	have "parallelogram G B E F" using `parallelogram G B E F` .
	have "parallel G F B E" using parallelogram_f[OF `parallelogram G B E F`] by blast
	have "parallel H G A B" using parallelogram_f[OF `parallelogram H A B G`] by blast
	have "parallel B E G F" using parallelsymmetric[OF `parallel G F B E`] .
	have "parallel A B H G" using parallelsymmetric[OF `parallel H G A B`] .
	have "tarski_parallel B E G F" using paralleldef2B[OF `parallel B E G F`] .
	have "tarski_parallel A B H G" using paralleldef2B[OF `parallel A B H G`] .
	have "same_side G F B E" using tarski_parallel_f[OF `tarski_parallel B E G F`] by blast
	have "same_side H G A B" using tarski_parallel_f[OF `tarski_parallel A B H G`] by blast
	have "col A B E" using collinear_b `bet A B E` by blast
	have "A \<noteq> E" using betweennotequal[OF `bet A B E`] by blast
	have "same_side H G A E" using samesidecollinear[OF `same_side H G A B` `col A B E` `A \<noteq> E`] .
	have "same_side G F E B" using samesideflip[OF `same_side G F B E`] .
	have "col E B A" using collinearorder[OF `col A B E`] by blast
	have "E \<noteq> A" using inequalitysymmetric[OF `A \<noteq> E`] .
	have "same_side G F E A" using samesidecollinear[OF `same_side G F E B` `col E B A` `E \<noteq> A`] .
	have "same_side G F A E" using samesideflip[OF `same_side G F E A`] .
	have "same_side H F A E" using samesidetransitive[OF `same_side H G A E` `same_side G F A E`] .
	have "parallel H A F E \<and> seg_eq H A F E \<and> same_side H F A E" using `parallel H A F E` `seg_eq H A F E` `same_side H F A E` by blast
	have "parallel H F A E" using Prop33B[OF `parallel H A F E` `seg_eq H A F E` `same_side H F A E`] by blast
	have "parallel H A E F" using parallelflip[OF `parallel H A F E`] by blast
	have "parallelogram H A E F" using parallelogram_b[OF `parallel H A E F` `parallel H F A E`] .
	have "\<not> col H F E" using parallelNC[OF `parallel H A F E`] by blast
	have "\<not> col E F H" using NCorder[OF `\<not> col H F E`] by blast
	obtain t where "midpoint H t E \<and> midpoint A t F" using diagonalsbisect[OF `parallelogram H A E F`]  by  blast
	have "midpoint H t E" using `midpoint H t E \<and> midpoint A t F` by blast
	have "midpoint A t F" using `midpoint H t E \<and> midpoint A t F` by blast
	have "bet H t E \<and> seg_eq H t t E" using midpoint_f[OF `midpoint H t E`] .
	have "seg_eq H t t E" using `bet H t E \<and> seg_eq H t t E` by blast
	have "bet A t F \<and> seg_eq A t t F" using midpoint_f[OF `midpoint A t F`] .
	have "seg_eq A t t F" using `bet A t F \<and> seg_eq A t t F` by blast
	have "seg_eq A t F t" using congruenceflip[OF `seg_eq A t t F`] by blast
	have "bet A t F" using `bet A t F \<and> seg_eq A t t F` by blast
	have "bet H t E" using `bet H t E \<and> seg_eq H t t E` by blast
	have "bet A B E" using `bet A B E` .
	have "seg_eq H t E t" using congruenceflip[OF `seg_eq H t t E`] by blast
	have "seg_eq t A t F" using congruenceflip[OF `seg_eq A t F t`] by blast
	have "\<not> col H E F" using NCorder[OF `\<not> col E F H`] by blast
	obtain K where "bet H B K \<and> bet F E K" using Euclid5E[OF `bet A t F` `bet H t E` `bet A B E` `seg_eq H t E t` `seg_eq t A t F`]  by  blast
	have "bet F E K" using `bet H B K \<and> bet F E K` by blast
	have "col F E K" using collinear_b `bet H B K \<and> bet F E K` by blast
	have "col E F K" using collinearorder[OF `col F E K`] by blast
	have "F \<noteq> K" using betweennotequal[OF `bet F E K`] by blast
	have "K \<noteq> F" using inequalitysymmetric[OF `F \<noteq> K`] .
	have "parallel H A K F" using collinearparallel[OF `parallel H A E F` `col E F K` `K \<noteq> F`] .
	have "parallel H A F K" using parallelflip[OF `parallel H A K F`] by blast
	have "parallel F K H A" using parallelsymmetric[OF `parallel H A F K`] .
	have "parallel F K A H" using parallelflip[OF `parallel F K H A`] by blast
	have "H = H" using equalityreflexiveE.
	have "col A H H" using collinear_b `H = H` by blast
	obtain L where "parallelogram H L K F \<and> col A H L" using triangletoparallelogram[OF `parallel F K A H` `col A H H`]  by  blast
	have "parallelogram H L K F" using `parallelogram H L K F \<and> col A H L` by blast
	have "col A H L" using `parallelogram H L K F \<and> col A H L` by blast
	have "parallel H L K F" using parallelogram_f[OF `parallelogram H L K F`] by blast
	have "\<not> col L K F" using parallelNC[OF `parallel H L K F`] by blast
	have "L \<noteq> K" using NCdistinct[OF `\<not> col L K F`] by blast
	have "K \<noteq> L" using inequalitysymmetric[OF `L \<noteq> K`] .
	have "parallelogram G B E F" using `parallelogram G B E F` .
	have "parallel G B E F" using parallelogram_f[OF `parallelogram G B E F`] by blast
	have "parallel G B F E" using parallelflip[OF `parallel G B E F`] by blast
	have "col F E E" using collinear_b `E = E` by blast
	have "col F E K" using collinear_b `bet H B K \<and> bet F E K` by blast
	have "E \<noteq> K" using betweennotequal[OF `bet F E K`] by blast
	have "parallel G B E K" using collinearparallel2[OF `parallel G B F E` `col F E E` `col F E K` `E \<noteq> K`] .
	have "parallel E K G B" using parallelsymmetric[OF `parallel G B E K`] .
	have "col G B B" using collinear_b `B = B` by blast
	obtain M where "parallelogram B M K E \<and> col G B M" using triangletoparallelogram[OF `parallel E K G B` `col G B B`]  by  blast
	have "parallelogram H L K F" using `parallelogram H L K F` .
	have "parallelogram L K F H" using PGrotate[OF `parallelogram H L K F`] .
	have "parallelogram K L H F" using PGflip[OF `parallelogram L K F H`] .
	have "parallelogram L H F K" using PGrotate[OF `parallelogram K L H F`] .
	have "parallelogram H F K L" using PGrotate[OF `parallelogram L H F K`] .
	have "bet F E K" using `bet F E K` .
	have "bet A B E" using `bet A B E` .
	have "parallelogram H A B G" using `parallelogram H A B G` .
	have "parallelogram A H G B" using PGflip[OF `parallelogram H A B G`] .
	have "parallel A H G B" using parallelogram_f[OF `parallelogram A H G B`] by blast
	have "K = K" using equalityreflexiveE.
	have "E = E" using equalityreflexiveE.
	have "F = F" using equalityreflexiveE.
	have "bet H B K" using `bet H B K \<and> bet F E K` by blast
	have "parallelogram B M K E" using `parallelogram B M K E \<and> col G B M` by blast
	have "parallel B E M K" using parallelogram_f[OF `parallelogram B M K E`] by blast
	have "parallel M K B E" using parallelsymmetric[OF `parallel B E M K`] .
	have "parallel K M E B" using parallelflip[OF `parallel M K B E`] by blast
	have "parallelogram G B E F" using `parallelogram G B E F` .
	have "parallel G F B E" using parallelogram_f[OF `parallelogram G B E F`] by blast
	have "\<not> col E M K" using parallelNC[OF `parallel B E M K`] by blast
	have "\<not> col B E K" using parallelNC[OF `parallel B E M K`] by blast
	have "\<not> col G F B" using parallelNC[OF `parallel G F A B`] by blast
	have "parallel M K B E" using parallelflip[OF `parallel K M E B`] by blast
	have "parallel G F B E" using parallelflip[OF `parallel G F E B`] by blast
	have "bet K E F" using betweennesssymmetryE[OF `bet F E K`] .
	have "col M K K" using collinear_b `K = K` by blast
	have "col B E E" using collinear_b `E = E` by blast
	have "col G F F" using collinear_b `F = F` by blast
	have "M \<noteq> K" using NCdistinct[OF `\<not> col E M K`] by blast
	have "B \<noteq> E" using NCdistinct[OF `\<not> col B E K`] by blast
	have "G \<noteq> F" using NCdistinct[OF `\<not> col G F B`] by blast
	have "parallel M K G F" using Prop30[OF `parallel M K B E` `parallel G F B E` `bet K E F` `col M K K` `col B E E` `col G F F` `M \<noteq> K` `B \<noteq> E` `G \<noteq> F`] .
	have "parallel K M F G" using parallelflip[OF `parallel M K G F`] by blast
	have "parallel F G K M" using parallelsymmetric[OF `parallel K M F G`] .
	have "parallelogram H L K F" using `parallelogram H L K F` .
	have "parallel H F L K" using parallelogram_f[OF `parallelogram H L K F`] by blast
	have "parallel L K H F" using parallelsymmetric[OF `parallel H F L K`] .
	have "parallel K L H F" using parallelflip[OF `parallel L K H F`] by blast
	have "col H F G" using collinearorder[OF `col G H F`] by blast
	have "parallel K L G F" using collinearparallel[OF `parallel K L H F` `col H F G` `G \<noteq> F`] .
	have "parallel K L F G" using parallelflip[OF `parallel K L G F`] by blast
	have "parallel F G K L" using parallelsymmetric[OF `parallel K L F G`] .
	have "col K M L" using Playfair[OF `parallel F G K M` `parallel F G K L`] .
	have "col M K L" using collinearorder[OF `col K M L`] by blast
	have "parallel B E M K" using parallelogram_f[OF `parallelogram B M K E`] by blast
	have "L \<noteq> K" using inequalitysymmetric[OF `K \<noteq> L`] .
	have "parallel B E L K" using collinearparallel[OF `parallel B E M K` `col M K L` `L \<noteq> K`] .
	have "parallel L K B E" using parallelsymmetric[OF `parallel B E L K`] .
	have "parallel L K E B" using parallelflip[OF `parallel L K B E`] by blast
	have "col A B E" using collinear_b `bet A B E` by blast
	have "col E B A" using collinearorder[OF `col A B E`] by blast
	have "parallel L K A B" using collinearparallel[OF `parallel L K E B` `col E B A` `A \<noteq> B`] .
	have "parallel A B L K" using parallelsymmetric[OF `parallel L K A B`] .
	have "parallel A B K L" using parallelflip[OF `parallel A B L K`] by blast
	have "bet K B H" using betweennesssymmetryE[OF `bet H B K`] .
	have "col L A H" using collinearorder[OF `col A H L`] by blast
	have "bet L A H" using parallelbetween[OF `bet K B H` `parallel A B K L` `col L A H`] .
	have "bet H A L" using betweennesssymmetryE[OF `bet L A H`] .
	have "parallel H A G B" using parallelflip[OF `parallel A H G B`] by blast
	have "col G B M" using `parallelogram B M K E \<and> col G B M` by blast
	have "\<not> col B M K" using parallelNC[OF `parallel B E M K`] by blast
	have "M \<noteq> B" using NCdistinct[OF `\<not> col B M K`] by blast
	have "parallel H A M B" using collinearparallel[OF `parallel H A G B` `col G B M` `M \<noteq> B`] .
	have "parallel M B H A" using parallelsymmetric[OF `parallel H A M B`] .
	have "parallel M B A H" using parallelflip[OF `parallel M B H A`] by blast
	have "col A H L" using collinearorder[OF `col L A H`] by blast
	have "parallelogram H L K F" using `parallelogram H L K F` .
	have "parallel H L K F" using parallelogram_f[OF `parallelogram H L K F`] by blast
	have "\<not> col H L K" using parallelNC[OF `parallel H F L K`] by blast
	have "L \<noteq> H" using NCdistinct[OF `\<not> col H L K`] by blast
	have "parallel M B L H" using collinearparallel[OF `parallel M B A H` `col A H L` `L \<noteq> H`] .
	have "parallel M B H L" using parallelflip[OF `parallel M B L H`] by blast
	have "col L M K" using collinearorder[OF `col K M L`] by blast
	have "bet L M K" using parallelbetween[OF `bet H B K` `parallel M B H L` `col L M K`] .
	have "parallelogram G B E F" using `parallelogram G B E F` .
	have "parallel G B E F" using parallelogram_f[OF `parallelogram G B E F`] by blast
	have "col F E K" using collinear_b `bet H B K \<and> bet F E K` by blast
	have "col E F K" using collinearorder[OF `col F E K`] by blast
	have "F \<noteq> K" using betweennotequal[OF `bet F E K`] by blast
	have "K \<noteq> F" using inequalitysymmetric[OF `F \<noteq> K`] .
	have "parallel G B K F" using collinearparallel[OF `parallel G B E F` `col E F K` `K \<noteq> F`] .
	have "col F G H" using collinearorder[OF `col G H F`] by blast
	have "bet F G H" using parallelbetween[OF `bet K B H` `parallel G B K F` `col F G H`] .
	have "bet H G F" using betweennesssymmetryE[OF `bet F G H`] .
	have "parallelogram H A B G" using `parallelogram H A B G` .
	have "parallelogram A B G H" using PGrotate[OF `parallelogram H A B G`] .
	have "parallelogram B G H A" using PGrotate[OF `parallelogram A B G H`] .
	have "parallelogram G H A B" using PGrotate[OF `parallelogram B G H A`] .
	have "parallelogram M K E B" using PGrotate[OF `parallelogram B M K E`] .
	have "parallelogram K E B M" using PGrotate[OF `parallelogram M K E B`] .
	have "parallelogram E B M K" using PGrotate[OF `parallelogram K E B M`] .
	have "qua_eq_area B E F G L M B A" using Prop43[OF `parallelogram H F K L` `bet H A L` `bet H G F` `bet L M K` `bet F E K` `bet H B K` `parallelogram G H A B` `parallelogram E B M K`] .
	have "parallelogram H L K F" using `parallelogram H L K F` .
	have "bet H G F" using `bet H G F` .
	have "bet H A L" using `bet H A L` .
	have "bet L M K" using `bet L M K` .
	have "parallelogram A H G B" using PGflip[OF `parallelogram H A B G`] .
	have "parallelogram M B E K" using PGflip[OF `parallelogram B M K E`] .
	have "parallelogram A B M L" using Prop43B[OF `parallelogram H L K F` `bet H G F` `bet H A L` `bet F E K` `bet L M K` `parallelogram A H G B` `parallelogram M B E K`] .
	have "ang_eq E B G J D N" using `ang_eq E B G J D N` .
	have "bet A B E" using `bet A B E` .
	have "col H G F" using collinearorder[OF `col F G H`] by blast
	have "col L M K" using `col L M K` .
	have "H \<noteq> F" using betweennotequal[OF `bet H G F`] by blast
	have "L \<noteq> K" using betweennotequal[OF `bet L M K`] by blast
	have "H \<noteq> G" using betweennotequal[OF `bet H G F`] by blast
	have "M \<noteq> K" using betweennotequal[OF `bet L M K`] by blast
	have "parallel H F L K" using parallelogram_f[OF `parallelogram H L K F`] by blast
	have "\<not> (meets H F L K)" using parallel_f[OF `parallel H F L K`] by fastforce
	have "bet H B K" using `bet H B K` .
	have "col G M B" using collinearorder[OF `col G B M`] by blast
	have "bet G B M" using collinearbetween[OF `col H G F` `col L M K` `H \<noteq> F` `L \<noteq> K` `H \<noteq> G` `M \<noteq> K` `\<not> (meets H F L K)` `bet H B K` `col G M B`] .
	have "ang_eq A B M G B E" using Prop15[OF `bet G B M` `bet A B E` `\<not> col G B A`] by blast
	have "ang_eq G B E E B G" using ABCequalsCBA[OF `\<not> col G B E`] .
	have "ang_eq A B M E B G" using equalanglestransitive[OF `ang_eq A B M G B E` `ang_eq G B E E B G`] .
	have "ang_eq A B M J D N" using equalanglestransitive[OF `ang_eq A B M E B G` `ang_eq E B G J D N`] .
	have "parallelogram A B M L \<and> ang_eq A B M J D N \<and> qua_eq_area B E F G L M B A \<and> bet G B M" using `parallelogram A B M L` `ang_eq A B M J D N` `qua_eq_area B E F G L M B A` `bet G B M` by blast
	thus ?thesis by blast
qed

end