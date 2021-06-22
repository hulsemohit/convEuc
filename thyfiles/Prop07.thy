theory Prop07
	imports Axioms Definitions Theorems
begin

theorem Prop07:
	assumes: `axioms`
		"A \<noteq> B"
		"seg_eq C A D A"
		"seg_eq C B D B"
		"same_side C D A B"
	shows: "C = D"
proof -
	have "\<not> col A B C" using sameside_f[OF `axioms` `same_side C D A B`] by blast
	obtain F where "perp_at C F A B F" using Prop12[OF `axioms` `A \<noteq> B` `\<not> col A B C`] by blast
	obtain H where "col C F F \<and> col A B F \<and> col A B H \<and> ang_right H F C" using perpat_f[OF `axioms` `perp_at C F A B F`] by blast
	have "col A B F" using `col C F F \<and> col A B F \<and> col A B H \<and> ang_right H F C` by blast
	have "col A B H" using `col C F F \<and> col A B F \<and> col A B H \<and> ang_right H F C` by blast
	have "\<not> (C = F)"
	proof (rule ccontr)
		assume "C = F"
		have "col A B C" using `col A B F` `C = F` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "C \<noteq> F" by blast
	have "C \<noteq> F" using `C \<noteq> F` .
	have "F \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> F`] .
	obtain E where "bet C F E \<and> seg_eq F E F C" using extensionE[OF `axioms` `C \<noteq> F` `F \<noteq> C`] by blast
	have "bet C F E" using `bet C F E \<and> seg_eq F E F C` by blast
	have "seg_eq F E F C" using `bet C F E \<and> seg_eq F E F C` by blast
	consider "A = F"|"A \<noteq> F" by blast
	hence seg_eq A C A E
	proof (cases)
		case 1
		have "seg_eq F E F C" using `seg_eq F E F C` .
		have "seg_eq A E A C" using `seg_eq F E F C` `A = F` `A = F` by blast
		have "seg_eq A C A E" using congruencesymmetric[OF `axioms` `seg_eq A E A C`] .
	next
		case 2
		have "col A B F" using `col A B F` .
		have "col A B H" using `col A B H` .
		have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
		have "col B A F" using collinearorder[OF `axioms` `col A B F`] by blast
		have "col B A H" using collinearorder[OF `axioms` `col A B H`] by blast
		have "col A F H" using collinear4[OF `axioms` `col B A F` `col B A H` `B \<noteq> A`] .
		have "col H F A" using collinearorder[OF `axioms` `col A F H`] by blast
		have "ang_right H F C" using `col C F F \<and> col A B F \<and> col A B H \<and> ang_right H F C` by blast
		have "ang_right A F C" using collinearright[OF `axioms` `ang_right H F C` `col H F A` `A \<noteq> F`] .
		have "ang_right C F A" using n8_2[OF `axioms` `ang_right A F C`] .
		obtain P where "bet C F P \<and> seg_eq C F P F \<and> seg_eq C A P A \<and> F \<noteq> A" using rightangle_f[OF `axioms` `ang_right C F A`] by blast
		have "seg_eq C A P A" using `bet C F P \<and> seg_eq C F P F \<and> seg_eq C A P A \<and> F \<noteq> A` by blast
		have "bet C F E" using `bet C F E` .
		have "bet C F P" using `bet C F P \<and> seg_eq C F P F \<and> seg_eq C A P A \<and> F \<noteq> A` by blast
		have "seg_eq C F P F" using `bet C F P \<and> seg_eq C F P F \<and> seg_eq C A P A \<and> F \<noteq> A` by blast
		have "seg_eq F E F C" using `seg_eq F E F C` .
		have "seg_eq F E C F" using congruenceflip[OF `axioms` `seg_eq F E F C`] by blast
		have "seg_eq F E P F" using congruencetransitive[OF `axioms` `seg_eq F E C F` `seg_eq C F P F`] .
		have "seg_eq F E F P" using congruenceflip[OF `axioms` `seg_eq F E P F`] by blast
		have "E = P" using extensionunique[OF `axioms` `bet C F E` `bet C F P` `seg_eq F E F P`] .
		have "seg_eq C A E A" using `seg_eq C A P A` `E = P` by blast
		have "seg_eq A C A E" using congruenceflip[OF `axioms` `seg_eq C A E A`] by blast
	next
	consider "B = F"|"B \<noteq> F" by blast
	hence seg_eq B C B E
	proof (cases)
		case 1
		have "seg_eq F E F C" using `seg_eq F E F C` .
		have "seg_eq B E B C" using `seg_eq F E F C` `B = F` `B = F` by blast
		have "seg_eq B C B E" using congruencesymmetric[OF `axioms` `seg_eq B E B C`] .
	next
		case 2
		have "col A B F" using `col A B F` .
		have "col B A F" using collinearorder[OF `axioms` `col A B F`] by blast
		have "col B A H" using collinearorder[OF `axioms` `col A B H`] by blast
		have "A \<noteq> B" using `A \<noteq> B` .
		have "col A B F" using collinearorder[OF `axioms` `col B A F`] by blast
		have "col A B H" using collinearorder[OF `axioms` `col B A H`] by blast
		have "col B F H" using collinear4[OF `axioms` `col A B F` `col A B H` `A \<noteq> B`] .
		have "col H F B" using collinearorder[OF `axioms` `col B F H`] by blast
		have "ang_right H F C" using `col C F F \<and> col A B F \<and> col A B H \<and> ang_right H F C` by blast
		have "ang_right B F C" using collinearright[OF `axioms` `ang_right H F C` `col H F B` `B \<noteq> F`] .
		have "ang_right C F B" using n8_2[OF `axioms` `ang_right B F C`] .
		obtain P where "bet C F P \<and> seg_eq C F P F \<and> seg_eq C B P B \<and> F \<noteq> B" using rightangle_f[OF `axioms` `ang_right C F B`] by blast
		have "seg_eq C B P B" using `bet C F P \<and> seg_eq C F P F \<and> seg_eq C B P B \<and> F \<noteq> B` by blast
		have "bet C F E" using `bet C F E` .
		have "bet C F P" using `bet C F P \<and> seg_eq C F P F \<and> seg_eq C B P B \<and> F \<noteq> B` by blast
		have "seg_eq C F P F" using `bet C F P \<and> seg_eq C F P F \<and> seg_eq C B P B \<and> F \<noteq> B` by blast
		have "seg_eq F E F C" using `seg_eq F E F C` .
		have "seg_eq F E C F" using congruenceflip[OF `axioms` `seg_eq F E F C`] by blast
		have "seg_eq F E P F" using congruencetransitive[OF `axioms` `seg_eq F E C F` `seg_eq C F P F`] .
		have "seg_eq F E F P" using congruenceflip[OF `axioms` `seg_eq F E P F`] by blast
		have "E = P" using extensionunique[OF `axioms` `bet C F E` `bet C F P` `seg_eq F E F P`] .
		have "seg_eq C B E B" using `seg_eq C B P B` `E = P` by blast
		have "seg_eq B C B E" using congruenceflip[OF `axioms` `seg_eq C B E B`] by blast
	next
	have "oppo_side C A B E" using oppositeside_b[OF `axioms` `bet C F E` `col A B F` `\<not> col A B C`] .
	have "same_side D C A B" using samesidesymmetric[OF `axioms` `same_side C D A B`] by blast
	have "oppo_side D A B E" using planeseparation[OF `axioms` `same_side D C A B` `oppo_side C A B E`] .
	obtain G where "bet D G E \<and> col A B G \<and> \<not> col A B D" using oppositeside_f[OF `axioms` `oppo_side D A B E`] by blast
	have "bet D G E" using `bet D G E \<and> col A B G \<and> \<not> col A B D` by blast
	have "col A B G" using `bet D G E \<and> col A B G \<and> \<not> col A B D` by blast
	have "seg_eq A C A E" using `seg_eq A C A E` .
	have "seg_eq C A D A" using `seg_eq C A D A` .
	have "seg_eq E A C A" using doublereverse[OF `axioms` `seg_eq A C A E`] by blast
	have "seg_eq A E C A" using congruenceflip[OF `axioms` `seg_eq E A C A`] by blast
	have "seg_eq A E D A" using congruencetransitive[OF `axioms` `seg_eq A E C A` `seg_eq C A D A`] .
	have "seg_eq A E A D" using congruenceflip[OF `axioms` `seg_eq A E D A`] by blast
	have "seg_eq A D A E" using congruencesymmetric[OF `axioms` `seg_eq A E A D`] .
	have "seg_eq B D B C" using doublereverse[OF `axioms` `seg_eq C B D B`] by blast
	have "seg_eq B D B E" using congruencetransitive[OF `axioms` `seg_eq B D B C` `seg_eq B C B E`] .
	have "seg_eq A G A G" using congruencereflexiveE[OF `axioms`] by blast
	have "seg_eq G B G B" using congruencereflexiveE[OF `axioms`] by blast
	have "col A B G" using `col A B G` .
	have "A = B \<or> A = G \<or> B = G \<or> bet B A G \<or> bet A B G \<or> bet A G B" using collinear_f[OF `axioms` `col A B G`] .
	consider "A = B"|"A = G"|"B = G"|"bet B A G"|"bet A B G"|"bet A G B" using `A = B \<or> A = G \<or> B = G \<or> bet B A G \<or> bet A B G \<or> bet A G B`  by blast
	hence seg_eq G D G E
	proof (cases)
		case 1
		have "seg_eq G D G E"
		proof (rule ccontr)
			assume "\<not> (seg_eq G D G E)"
			have "A \<noteq> B" using `A \<noteq> B` .
			show "False" using `A \<noteq> B` `A = B` by blast
		qed
		hence "seg_eq G D G E" by blast
	next
		case 2
		have "seg_eq A D A E" using congruencesymmetric[OF `axioms` `seg_eq A E A D`] .
		have "seg_eq G D G E" using `seg_eq A D A E` `A = G` `A = G` by blast
	next
		case 3
		have "seg_eq B D B E" using `seg_eq B D B E` .
		have "seg_eq G D G E" using `seg_eq B D B E` `B = G` `B = G` by blast
	next
		case 4
		have "seg_eq B A B A" using congruencereflexiveE[OF `axioms`] by blast
		have "seg_eq A G A G" using congruencereflexiveE[OF `axioms`] by blast
		have "seg_eq B D B E" using `seg_eq B D B E` .
		have "seg_eq A D A E" using congruencesymmetric[OF `axioms` `seg_eq A E A D`] .
		have "seg_eq D G E G" using 5-lineE[OF `axioms` `seg_eq A G A G` `seg_eq B D B E` `seg_eq A D A E` `bet B A G` `bet B A G` `seg_eq B A B A`] .
		have "seg_eq G D G E" using congruenceflip[OF `axioms` `seg_eq D G E G`] by blast
	next
		case 4
		have "seg_eq A B A B" using congruencereflexiveE[OF `axioms`] by blast
		have "seg_eq B G B G" using congruencereflexiveE[OF `axioms`] by blast
		have "seg_eq A D A E" using `seg_eq A D A E` .
		have "seg_eq B D B E" using `seg_eq B D B E` .
		have "seg_eq D G E G" using 5-lineE[OF `axioms` `seg_eq B G B G` `seg_eq A D A E` `seg_eq B D B E` `bet A B G` `bet A B G` `seg_eq A B A B`] .
		have "seg_eq G D G E" using congruenceflip[OF `axioms` `seg_eq D G E G`] by blast
	next
		case 5
		have "seg_eq A G A G" using congruencereflexiveE[OF `axioms`] by blast
		have "seg_eq G B G B" using congruencereflexiveE[OF `axioms`] by blast
		have "seg_eq A D A E" using `seg_eq A D A E` .
		have "seg_eq B D B E" using `seg_eq B D B E` .
		have "seg_eq G D G E" using interior5[OF `axioms` `bet A G B` `bet A G B` `seg_eq A G A G` `seg_eq G B G B` `seg_eq A D A E` `seg_eq B D B E`] .
	next
	have "seg_eq B D B E" using `seg_eq B D B E` .
	have "seg_eq D A E A" using congruenceflip[OF `axioms` `seg_eq A D A E`] by blast
	consider "A = G"|"A \<noteq> G" by blast
	hence F = G
	proof (cases)
		case 1
		have "bet E G D" using betweennesssymmetryE[OF `axioms` `bet D G E`] .
		have "seg_eq E G D G" using doublereverse[OF `axioms` `seg_eq G D G E`] by blast
		have "seg_eq E B D B" using doublereverse[OF `axioms` `seg_eq B D B E`] by blast
		have "\<not> (G = B)"
		proof (rule ccontr)
			assume "G = B"
			have "A = B" using `A = G` `G = B` by blast
			show "False" using `A = B` `A \<noteq> B` by blast
		qed
		hence "G \<noteq> B" by blast
		have "ang_right E G B" using rightangle_b[OF `axioms` `bet E G D` `seg_eq E G D G` `seg_eq E B D B` `G \<noteq> B`] .
		have "bet E F C" using betweennesssymmetryE[OF `axioms` `bet C F E`] .
		have "seg_eq E F C F" using doublereverse[OF `axioms` `seg_eq F E F C`] by blast
		have "seg_eq E B C B" using doublereverse[OF `axioms` `seg_eq B C B E`] by blast
		have "\<not> (F = B)"
		proof (rule ccontr)
			assume "F = B"
			have "seg_eq A E A D" using congruenceflip[OF `axioms` `seg_eq A E D A`] by blast
			have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
			have "bet E A D" using `bet E G D` `A = G` by blast
			have "seg_eq E A D A" using congruenceflip[OF `axioms` `seg_eq A E A D`] by blast
			have "seg_eq E B D B" using `seg_eq E B D B` .
			have "A \<noteq> B" using `A \<noteq> B` .
			have "ang_right E A B" using rightangle_b[OF `axioms` `bet E A D` `seg_eq E A D A` `seg_eq E B D B` `A \<noteq> B`] .
			have "ang_right B A E" using n8_2[OF `axioms` `ang_right E A B`] .
			have "bet E B C" using `bet E F C` `F = B` by blast
			have "seg_eq E B C B" using `seg_eq E B C B` .
			have "seg_eq E A C A" using `seg_eq E A C A` .
			have "B \<noteq> A" using `B \<noteq> A` .
			have "ang_right E B A" using rightangle_b[OF `axioms` `bet E B C` `seg_eq E B C B` `seg_eq E A C A` `B \<noteq> A`] .
			obtain J where "bet B A J \<and> seg_eq A J A B" using extensionE[OF `axioms` `B \<noteq> A` `A \<noteq> B`] by blast
			have "bet B A J" using `bet B A J \<and> seg_eq A J A B` by blast
			have "ray_on B A J" using ray4 `axioms` `bet B A J \<and> seg_eq A J A B` `B \<noteq> A` by blast
			have "ang_right E B J" using n8_3[OF `axioms` `ang_right E B A` `ray_on B A J`] .
			have "ang_right J B E" using n8_2[OF `axioms` `ang_right E B J`] .
			have "col A B J" using collinear_b `axioms` `bet B A J \<and> seg_eq A J A B` by blast
			have "ang_right E A B" using `ang_right E A B` .
			have "col B A J" using collinearorder[OF `axioms` `col A B J`] by blast
			have "ang_right B A E" using n8_2[OF `axioms` `ang_right E A B`] .
			have "A \<noteq> J" using betweennotequal[OF `axioms` `bet B A J`] by blast
			have "J \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> J`] .
			have "ang_right J A E" using collinearright[OF `axioms` `ang_right B A E` `col B A J` `J \<noteq> A`] .
			have "ang_right J B E" using `ang_right J B E` .
			have "col J A B" using collinearorder[OF `axioms` `col A B J`] by blast
			have "A = B" using droppedperpendicularunique[OF `axioms` `ang_right J A E` `ang_right J B E` `col J A B`] .
			have "A \<noteq> B" using `A \<noteq> B` .
			show "False" using `A \<noteq> B` `A = B` by blast
		qed
		hence "F \<noteq> B" by blast
		have "ang_right E F B" using rightangle_b[OF `axioms` `bet E F C` `seg_eq E F C F` `seg_eq E B C B` `F \<noteq> B`] .
		have "ang_right B G E" using n8_2[OF `axioms` `ang_right E G B`] .
		have "ang_right B F E" using n8_2[OF `axioms` `ang_right E F B`] .
		have "col A B G" using `col A B G` .
		have "col A B F" using `col A B F` .
		have "A \<noteq> B" using `A \<noteq> B` .
		have "col B G F" using collinear4[OF `axioms` `col A B G` `col A B F` `A \<noteq> B`] .
		have "G = F" using droppedperpendicularunique[OF `axioms` `ang_right B G E` `ang_right B F E` `col B G F`] .
		have "F = G" using equalitysymmetric[OF `axioms` `G = F`] .
	next
		case 2
		consider "A = F"|"A \<noteq> F" by blast
		hence F = G
		proof (cases)
			case 1
			have "F \<noteq> B" using `A \<noteq> B` `A = F` by blast
			have "seg_eq E F C F" using congruenceflip[OF `axioms` `seg_eq F E F C`] by blast
			have "seg_eq E B C B" using doublereverse[OF `axioms` `seg_eq B C B E`] by blast
			have "bet E F C" using betweennesssymmetryE[OF `axioms` `bet C F E`] .
			have "ang_right E F B" using rightangle_b[OF `axioms` `bet E F C` `seg_eq E F C F` `seg_eq E B C B` `F \<noteq> B`] .
			have "ang_right B F E" using n8_2[OF `axioms` `ang_right E F B`] .
			have "\<not> (B = G)"
			proof (rule ccontr)
				assume "B = G"
				have "seg_eq B E B D" using congruencesymmetric[OF `axioms` `seg_eq B D B E`] .
				have "bet E G D" using betweennesssymmetryE[OF `axioms` `bet D G E`] .
				have "bet E B D" using `bet E G D` `B = G` by blast
				have "seg_eq E B D B" using congruenceflip[OF `axioms` `seg_eq B E B D`] by blast
				have "seg_eq E A D A" using congruencesymmetric[OF `axioms` `seg_eq D A E A`] .
				have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
				have "ang_right E B A" using rightangle_b[OF `axioms` `bet E B D` `seg_eq E B D B` `seg_eq E A D A` `B \<noteq> A`] .
				have "ang_right A B E" using n8_2[OF `axioms` `ang_right E B A`] .
				have "bet E A C" using `bet E F C` `A = F` by blast
				have "seg_eq E A C A" using `seg_eq E A C A` .
				have "seg_eq E B C B" using `seg_eq E B C B` .
				have "ang_right E A B" using rightangle_b[OF `axioms` `bet E A C` `seg_eq E A C A` `seg_eq E B C B` `A \<noteq> B`] .
				obtain K where "bet A B K \<and> seg_eq B K B A" using extensionE[OF `axioms` `A \<noteq> B` `B \<noteq> A`] by blast
				have "bet A B K" using `bet A B K \<and> seg_eq B K B A` by blast
				have "ray_on A B K" using ray4 `axioms` `bet A B K \<and> seg_eq B K B A` `A \<noteq> B` by blast
				have "ang_right E A K" using n8_3[OF `axioms` `ang_right E A B` `ray_on A B K`] .
				have "ang_right K A E" using n8_2[OF `axioms` `ang_right E A K`] .
				have "col B A K" using collinear_b `axioms` `bet A B K \<and> seg_eq B K B A` by blast
				have "ang_right E B A" using `ang_right E B A` .
				have "col A B K" using collinearorder[OF `axioms` `col B A K`] by blast
				have "ang_right A B E" using n8_2[OF `axioms` `ang_right E B A`] .
				have "B \<noteq> K" using betweennotequal[OF `axioms` `bet A B K`] by blast
				have "K \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> K`] .
				have "ang_right K B E" using collinearright[OF `axioms` `ang_right A B E` `col A B K` `K \<noteq> B`] .
				have "ang_right K A E" using `ang_right K A E` .
				have "col K B A" using collinearorder[OF `axioms` `col A B K`] by blast
				have "B = A" using droppedperpendicularunique[OF `axioms` `ang_right K B E` `ang_right K A E` `col K B A`] .
				have "A \<noteq> B" using `A \<noteq> B` .
				have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
				show "False" using `B \<noteq> A` `B = A` by blast
			qed
			hence "B \<noteq> G" by blast
			have "G \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> G`] .
			have "seg_eq E G D G" using doublereverse[OF `axioms` `seg_eq G D G E`] by blast
			have "seg_eq E B D B" using doublereverse[OF `axioms` `seg_eq B D B E`] by blast
			have "bet E G D" using betweennesssymmetryE[OF `axioms` `bet D G E`] .
			have "ang_right E G B" using rightangle_b[OF `axioms` `bet E G D` `seg_eq E G D G` `seg_eq E B D B` `G \<noteq> B`] .
			have "ang_right B G E" using n8_2[OF `axioms` `ang_right E G B`] .
			have "col A B G" using `col A B G` .
			have "col F B G" using `col A B G` `A = F` by blast
			have "col B G F" using collinearorder[OF `axioms` `col F B G`] by blast
			have "G = F" using droppedperpendicularunique[OF `axioms` `ang_right B G E` `ang_right B F E` `col B G F`] .
			have "F = G" using equalitysymmetric[OF `axioms` `G = F`] .
		next
			case 2
			have "F \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> F`] .
			have "seg_eq E A C A" using `seg_eq E A C A` .
			have "seg_eq E F C F" using doublereverse[OF `axioms` `seg_eq F E F C`] by blast
			have "bet E F C" using betweennesssymmetryE[OF `axioms` `bet C F E`] .
			have "ang_right E F A" using rightangle_b[OF `axioms` `bet E F C` `seg_eq E F C F` `seg_eq E A C A` `F \<noteq> A`] .
			have "ang_right A F E" using n8_2[OF `axioms` `ang_right E F A`] .
			have "bet E G D" using betweennesssymmetryE[OF `axioms` `bet D G E`] .
			have "seg_eq E G D G" using doublereverse[OF `axioms` `seg_eq G D G E`] by blast
			have "seg_eq E A D A" using congruencesymmetric[OF `axioms` `seg_eq D A E A`] .
			have "G \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> G`] .
			have "ang_right E G A" using rightangle_b[OF `axioms` `bet E G D` `seg_eq E G D G` `seg_eq E A D A` `G \<noteq> A`] .
			have "ang_right A G E" using n8_2[OF `axioms` `ang_right E G A`] .
			have "col A B F" using `col A B F` .
			have "col A B G" using `col A B G` .
			have "col B A F" using collinearorder[OF `axioms` `col A B F`] by blast
			have "col B A G" using collinearorder[OF `axioms` `col A B G`] by blast
			have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
			have "col A F G" using collinear4[OF `axioms` `col B A F` `col B A G` `B \<noteq> A`] .
			have "F = G" using droppedperpendicularunique[OF `axioms` `ang_right A F E` `ang_right A G E` `col A F G`] .
		next
	next
	have "seg_eq B F B F" using congruencereflexiveE[OF `axioms`] by blast
	have "seg_eq A F A G" using `seg_eq A G A G` `F = G` by blast
	have "col A F B" using collinearorder[OF `axioms` `col A B F`] by blast
	have "A \<noteq> B" using `A \<noteq> B` .
	have "seg_eq A F A G" using `seg_eq A F A G` .
	have "seg_eq F B F B" using congruencereflexiveE[OF `axioms`] by blast
	have "seg_eq F B G B" using `seg_eq F B F B` `F = G` by blast
	have "seg_eq A C A D" using congruenceflip[OF `axioms` `seg_eq C A D A`] by blast
	have "seg_eq B C B D" using congruenceflip[OF `axioms` `seg_eq C B D B`] by blast
	have "seg_eq A B A B" using congruencereflexiveE[OF `axioms`] by blast
	have "seg_eq F C G D" using fiveline[OF `axioms` `col A F B` `seg_eq A F A G` `seg_eq F B G B` `seg_eq A C A D` `seg_eq B C B D` `seg_eq A B A B` `A \<noteq> B`] .
	have "seg_eq F C F D" using `seg_eq F C G D` `F = G` by blast
	have "bet E F C" using betweennesssymmetryE[OF `axioms` `bet C F E`] .
	have "bet E G D" using betweennesssymmetryE[OF `axioms` `bet D G E`] .
	have "bet E F D" using `bet E G D` `F = G` by blast
	have "ray_on F D C" using ray_b[OF `axioms` `bet E F C` `bet E F D`] .
	have "D = D" using equalityreflexiveE[OF `axioms`] .
	have "\<not> (F = D)"
	proof (rule ccontr)
		assume "F = D"
		have "col A B F" using collinearorder[OF `axioms` `col A F B`] by blast
		have "col A B D" using `col A B F` `F = D` by blast
		have "\<not> col A B D" using `bet D G E \<and> col A B G \<and> \<not> col A B D` by blast
		show "False" using `\<not> col A B D` `col A B D` by blast
	qed
	hence "F \<noteq> D" by blast
	have "ray_on F D D" using ray4 `axioms` `D = D` `F \<noteq> D` by blast
	have "C = D" using layoffunique[OF `axioms` `ray_on F D C` `ray_on F D D` `seg_eq F C F D`] .
	thus ?thesis by blast
qed

end