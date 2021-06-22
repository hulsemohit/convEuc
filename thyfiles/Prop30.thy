theory Prop30
	imports Axioms Definitions Theorems
begin

theorem Prop30:
	assumes: `axioms`
		"parallel A B E F"
		"parallel C D E F"
		"bet G H K"
		"col A B G"
		"col E F H"
		"col C D K"
		"A \<noteq> G"
		"E \<noteq> H"
		"C \<noteq> K"
	shows: "parallel A B C D"
proof -
	obtain b where "bet A G b \<and> seg_eq G b A G" using extensionE[OF `axioms` `A \<noteq> G` `A \<noteq> G`]  by  blast
	obtain f where "bet E H f \<and> seg_eq H f E H" using extensionE[OF `axioms` `E \<noteq> H` `E \<noteq> H`]  by  blast
	obtain d where "bet C K d \<and> seg_eq K d C K" using extensionE[OF `axioms` `C \<noteq> K` `C \<noteq> K`]  by  blast
	have "bet A G b" using `bet A G b \<and> seg_eq G b A G` by blast
	have "bet E H f" using `bet E H f \<and> seg_eq H f E H` by blast
	have "bet C K d" using `bet C K d \<and> seg_eq K d C K` by blast
	have "\<not> col C D E" using parallelNC[OF `axioms` `parallel C D E F`] by blast
	have "C \<noteq> D" using NCdistinct[OF `axioms` `\<not> col C D E`] by blast
	have "col A G b" using col_b `axioms` `bet A G b \<and> seg_eq G b A G` by blast
	have "col G A b" using collinearorder[OF `axioms` `col A G b`] by blast
	have "col G A B" using collinearorder[OF `axioms` `col A B G`] by blast
	have "G \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> G`] .
	have "col A b B" using collinear4[OF `axioms` `col G A b` `col G A B` `G \<noteq> A`] .
	have "col B A b" using collinearorder[OF `axioms` `col A b B`] by blast
	have "parallel E F A B" using parallelsymmetric[OF `axioms` `parallel A B E F`] .
	have "parallel E F B A" using parallelflip[OF `axioms` `parallel E F A B`] by blast
	have "A \<noteq> b" using betweennotequal[OF `axioms` `bet A G b`] by blast
	have "b \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> b`] .
	have "parallel E F b A" using collinearparallel[OF `axioms` `parallel E F B A` `col B A b` `b \<noteq> A`] .
	have "parallel E F A b" using parallelflip[OF `axioms` `parallel E F b A`] by blast
	have "parallel A b E F" using parallelsymmetric[OF `axioms` `parallel E F A b`] .
	have "col E H f" using col_b `axioms` `bet E H f \<and> seg_eq H f E H` by blast
	have "col H E f" using collinearorder[OF `axioms` `col E H f`] by blast
	have "col H E F" using collinearorder[OF `axioms` `col E F H`] by blast
	have "H \<noteq> E" using inequalitysymmetric[OF `axioms` `E \<noteq> H`] .
	have "col E f F" using collinear4[OF `axioms` `col H E f` `col H E F` `H \<noteq> E`] .
	have "col F E f" using collinearorder[OF `axioms` `col E f F`] by blast
	have "E \<noteq> f" using betweennotequal[OF `axioms` `bet E H f`] by blast
	have "f \<noteq> E" using inequalitysymmetric[OF `axioms` `E \<noteq> f`] .
	have "parallel A b F E" using parallelflip[OF `axioms` `parallel A b E F`] by blast
	have "parallel A b f E" using collinearparallel[OF `axioms` `parallel A b F E` `col F E f` `f \<noteq> E`] .
	have "parallel A b E f" using parallelflip[OF `axioms` `parallel A b f E`] by blast
	have "col C K d" using col_b `axioms` `bet C K d \<and> seg_eq K d C K` by blast
	have "col K C d" using collinearorder[OF `axioms` `col C K d`] by blast
	have "col K C D" using collinearorder[OF `axioms` `col C D K`] by blast
	have "K \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> K`] .
	have "col C d D" using collinear4[OF `axioms` `col K C d` `col K C D` `K \<noteq> C`] .
	have "col D C d" using collinearorder[OF `axioms` `col C d D`] by blast
	have "parallel E F C D" using parallelsymmetric[OF `axioms` `parallel C D E F`] .
	have "parallel E F D C" using parallelflip[OF `axioms` `parallel E F C D`] by blast
	have "C \<noteq> d" using betweennotequal[OF `axioms` `bet C K d`] by blast
	have "d \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> d`] .
	have "parallel E F d C" using collinearparallel[OF `axioms` `parallel E F D C` `col D C d` `d \<noteq> C`] .
	have "parallel E F C d" using parallelflip[OF `axioms` `parallel E F d C`] by blast
	have "parallel C d E F" using parallelsymmetric[OF `axioms` `parallel E F C d`] .
	have "parallel C d F E" using parallelflip[OF `axioms` `parallel C d E F`] by blast
	have "parallel C d f E" using collinearparallel[OF `axioms` `parallel C d F E` `col F E f` `f \<noteq> E`] .
	have "parallel C d E f" using parallelflip[OF `axioms` `parallel C d f E`] by blast
	have "H = H" using equalityreflexiveE[OF `axioms`] .
	have "col E H H" using col_b `axioms` `H = H` by blast
	have "bet G H K" using `bet G H K` .
	have "col A b G" using collinearorder[OF `axioms` `col A G b`] by blast
	have "col E f H" using collinearorder[OF `axioms` `col E H f`] by blast
	have "parallel A b E f" using `parallel A b E f` .
	have "col f E H" using collinearorder[OF `axioms` `col E H f`] by blast
	have "parallel A b f E" using parallelflip[OF `axioms` `parallel A b E f`] by blast
	have "parallel A b H E" using collinearparallel[OF `axioms` `parallel A b f E` `col f E H` `H \<noteq> E`] .
	have "parallel H E A b" using parallelsymmetric[OF `axioms` `parallel A b H E`] .
	have "parallel E H b A" using parallelflip[OF `axioms` `parallel H E A b`] by blast
	have "col b A G" using collinearorder[OF `axioms` `col A G b`] by blast
	have "parallel E H G A" using collinearparallel[OF `axioms` `parallel E H b A` `col b A G` `G \<noteq> A`] .
	have "parallel E H A G" using parallelflip[OF `axioms` `parallel E H G A`] by blast
	have "parallel A G E H" using parallelsymmetric[OF `axioms` `parallel E H A G`] .
	have "parallel C d E f" using `parallel C d E f` .
	have "parallel C d f E" using parallelflip[OF `axioms` `parallel C d E f`] by blast
	have "col f E H" using collinearorder[OF `axioms` `col E H f`] by blast
	have "parallel C d H E" using collinearparallel[OF `axioms` `parallel C d f E` `col f E H` `H \<noteq> E`] .
	have "parallel H E C d" using parallelsymmetric[OF `axioms` `parallel C d H E`] .
	have "parallel H E d C" using parallelflip[OF `axioms` `parallel H E C d`] by blast
	have "col C K d" using col_b `axioms` `bet C K d \<and> seg_eq K d C K` by blast
	have "col d C K" using collinearorder[OF `axioms` `col C K d`] by blast
	have "C \<noteq> K" using betweennotequal[OF `axioms` `bet C K d`] by blast
	have "K \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> K`] .
	have "parallel H E K C" using collinearparallel[OF `axioms` `parallel H E d C` `col d C K` `K \<noteq> C`] .
	have "parallel E H C K" using parallelflip[OF `axioms` `parallel H E K C`] by blast
	have "tarski_parallel E H C K" using paralleldef2B[OF `axioms` `parallel E H C K`] .
	have "same_side C K E H" sorry
	have "\<not> col E H K" using parallelNC[OF `axioms` `parallel E H C K`] by blast
	have "bet K H G" using betweennesssymmetryE[OF `axioms` `bet G H K`] .
	have "oppo_side K E H G" sorry
	have "oppo_side C E H G" using planeseparation[OF `axioms` `same_side C K E H` `oppo_side K E H G`] .
	obtain Q where "bet C Q G \<and> col E H Q \<and> \<not> col E H C" sorry
	have "bet C Q G" using `bet C Q G \<and> col E H Q \<and> \<not> col E H C` by blast
	have "col E H Q" using `bet C Q G \<and> col E H Q \<and> \<not> col E H C` by blast
	have "parallel C d E f" using `parallel C d E f` .
	have "parallel E f C d" using parallelsymmetric[OF `axioms` `parallel C d E f`] .
	have "tarski_parallel E f C d" using paralleldef2B[OF `axioms` `parallel E f C d`] .
	have "same_side C d E f" sorry
	have "same_side d C E f" using samesidesymmetric[OF `axioms` `same_side C d E f`] by blast
	have "col E H f" using col_b `axioms` `bet E H f \<and> seg_eq H f E H` by blast
	have "col H E f" using collinearorder[OF `axioms` `col E H f`] by blast
	have "col H E Q" using collinearorder[OF `axioms` `col E H Q`] by blast
	have "col E f Q" using collinear4[OF `axioms` `col H E f` `col H E Q` `H \<noteq> E`] .
	have "\<not> col C E f" using parallelNC[OF `axioms` `parallel C d E f`] by blast
	have "\<not> col E f C" using NCorder[OF `axioms` `\<not> col C E f`] by blast
	have "oppo_side C E f G" sorry
	have "oppo_side d E f G" using planeseparation[OF `axioms` `same_side d C E f` `oppo_side C E f G`] .
	obtain P where "bet d P G \<and> col E f P \<and> \<not> col E f d" sorry
	have "bet d P G" using `bet d P G \<and> col E f P \<and> \<not> col E f d` by blast
	have "cross A f G H \<or> cross A E G H"
	proof (rule ccontr)
		assume "\<not> (cross A f G H \<or> cross A E G H)"
		have "\<not> (cross A f G H) \<and> \<not> (cross A E G H)" using `\<not> (cross A f G H \<or> cross A E G H)` by blast
		have "\<not> (cross A f G H)" using `\<not> (cross A f G H) \<and> \<not> (cross A E G H)` by blast
		have "\<not> (cross A E G H)" using `\<not> (cross A f G H) \<and> \<not> (cross A E G H)` by blast
		have "cross A E G H" using n30helper[OF `axioms` `parallel A b E f` `bet A G b` `bet E H f` `\<not> (cross A f G H)`] .
		show "False" using `cross A E G H` `\<not> (cross A f G H) \<and> \<not> (cross A E G H)` by blast
	qed
	hence "cross A f G H \<or> cross A E G H" by blast
	have "cross C f K H \<or> cross C E K H"
	proof (rule ccontr)
		assume "\<not> (cross C f K H \<or> cross C E K H)"
		have "\<not> (cross C f K H) \<and> \<not> (cross C E K H)" using `\<not> (cross C f K H \<or> cross C E K H)` by blast
		have "\<not> (cross C f K H)" using `\<not> (cross C f K H) \<and> \<not> (cross C E K H)` by blast
		have "\<not> (cross C E K H)" using `\<not> (cross C f K H) \<and> \<not> (cross C E K H)` by blast
		have "cross C E K H" using n30helper[OF `axioms` `parallel C d E f` `bet C K d` `bet E H f` `\<not> (cross C f K H)`] .
		show "False" using `cross C E K H` `\<not> (cross C f K H) \<and> \<not> (cross C E K H)` by blast
	qed
	hence "cross C f K H \<or> cross C E K H" by blast
	have "col A B G" using `col A B G` .
	have "col E F H" using `col E F H` .
	have "col F E H" using collinearorder[OF `axioms` `col E F H`] by blast
	have "col B A G" using collinearorder[OF `axioms` `col A B G`] by blast
	have "parallel A B F E" using parallelflip[OF `axioms` `parallel A B E F`] by blast
	have "parallel A B H E" using collinearparallel[OF `axioms` `parallel A B F E` `col F E H` `H \<noteq> E`] .
	have "parallel A B E H" using parallelflip[OF `axioms` `parallel A B H E`] by blast
	have "parallel E H A B" using parallelsymmetric[OF `axioms` `parallel A B E H`] .
	have "parallel E H B A" using parallelflip[OF `axioms` `parallel E H A B`] by blast
	have "parallel E H G A" using collinearparallel[OF `axioms` `parallel E H B A` `col B A G` `G \<noteq> A`] .
	have "parallel E H A G" using parallelflip[OF `axioms` `parallel E H G A`] by blast
	have "parallel A G E H" using parallelsymmetric[OF `axioms` `parallel E H A G`] .
	have "\<not> col A G H" using parallelNC[OF `axioms` `parallel A G E H`] by blast
	have "parallel C D F E" using parallelflip[OF `axioms` `parallel C D E F`] by blast
	have "parallel C D H E" using collinearparallel[OF `axioms` `parallel C D F E` `col F E H` `H \<noteq> E`] .
	have "parallel C D E H" using parallelflip[OF `axioms` `parallel C D H E`] by blast
	have "parallel E H C D" using parallelsymmetric[OF `axioms` `parallel C D E H`] .
	have "parallel E H D C" using parallelflip[OF `axioms` `parallel E H C D`] by blast
	have "col D C K" using collinearorder[OF `axioms` `col C D K`] by blast
	have "parallel E H K C" using collinearparallel[OF `axioms` `parallel E H D C` `col D C K` `K \<noteq> C`] .
	have "parallel E H C K" using parallelflip[OF `axioms` `parallel E H K C`] by blast
	have "parallel C K E H" using parallelsymmetric[OF `axioms` `parallel E H C K`] .
	have "\<not> col C K H" using parallelNC[OF `axioms` `parallel C K E H`] by blast
	have "\<not> col K H C" using NCorder[OF `axioms` `\<not> col C K H`] by blast
	have "\<not> col E H K" using parallelNC[OF `axioms` `parallel E H C K`] by blast
	have "col E H f" using col_b `axioms` `bet E H f \<and> seg_eq H f E H` by blast
	have "H \<noteq> f" using betweennotequal[OF `axioms` `bet E H f`] by blast
	have "f \<noteq> H" using inequalitysymmetric[OF `axioms` `H \<noteq> f`] .
	have "H = H" using equalityreflexiveE[OF `axioms`] .
	have "col E H H" using col_b `axioms` `H = H` by blast
	have "\<not> col f H K" using NChelper[OF `axioms` `\<not> col E H K` `col E H f` `col E H H` `f \<noteq> H`] .
	have "\<not> col K H f" using NCorder[OF `axioms` `\<not> col f H K`] by blast
	have "col K H H" using col_b `axioms` `H = H` by blast
	consider "cross A f G H"|"cross A E G H" using `cross A f G H \<or> cross A E G H`  by blast
	hence parallel A b C d
	proof (cases)
		case 1
		have "oppo_side A G H f" using crossimpliesopposite[OF `axioms` `cross A f G H` `\<not> col A G H`] by blast
		consider "cross C f K H"|"cross C E K H" using `cross C f K H \<or> cross C E K H`  by blast
		hence parallel A b C d
		proof (cases)
			case 1
			have "oppo_side f H K C" using crossimpliesopposite[OF `axioms` `cross C f K H` `\<not> col C K H`] by blast
			have "parallel A b C d" using Prop30A[OF `axioms` `parallel A b E f` `parallel C d E f` `bet G H K` `bet A G b` `bet E H f` `bet C K d` `oppo_side A G H f` `oppo_side f H K C`] .
		next
			case 2
			obtain M where "bet C M E \<and> bet K M H" sorry
			have "bet C M E" using `bet C M E \<and> bet K M H` by blast
			have "bet K M H" using `bet C M E \<and> bet K M H` by blast
			have "col K M H" using col_b `axioms` `bet C M E \<and> bet K M H` by blast
			have "col K H M" using collinearorder[OF `axioms` `col K M H`] by blast
			have "bet f H E" using betweennesssymmetryE[OF `axioms` `bet E H f`] .
			have "col K H M \<and> col K H H \<and> col K H M \<and> bet f H E \<and> bet C M E \<and> \<not> col K H f \<and> \<not> col K H C" using `col K H M` `col K H H` `col K H M` `bet f H E` `bet C M E \<and> bet K M H` `\<not> col K H f` `\<not> col K H C` by blast
			have "same_side f C K H" sorry
			have "K = K" using equalityreflexiveE[OF `axioms`] .
			have "col K H K" using col_b `axioms` `K = K` by blast
			have "bet C K d \<and> col K H K \<and> \<not> col K H C" using `bet C K d \<and> seg_eq K d C K` `col K H K` `col K H M \<and> col K H H \<and> col K H M \<and> bet f H E \<and> bet C M E \<and> \<not> col K H f \<and> \<not> col K H C` by blast
			have "oppo_side C K H d" sorry
			have "oppo_side f K H d" using planeseparation[OF `axioms` `same_side f C K H` `oppo_side C K H d`] .
			obtain m where "bet f m d \<and> col K H m \<and> \<not> col K H f" sorry
			have "bet f m d" using `bet f m d \<and> col K H m \<and> \<not> col K H f` by blast
			have "col K H m" using `bet f m d \<and> col K H m \<and> \<not> col K H f` by blast
			have "parallel f E C d" using parallelsymmetric[OF `axioms` `parallel C d f E`] .
			have "\<not> (meets f E C d)" sorry
			have "C \<noteq> d" using `C \<noteq> d` .
			have "col f H E" using collinearorder[OF `axioms` `col E H f`] by blast
			have "col C K d" using `col C K d` .
			have "f \<noteq> E" using betweennotequal[OF `axioms` `bet f H E`] by blast
			have "f \<noteq> H" using inequalitysymmetric[OF `axioms` `H \<noteq> f`] .
			have "K \<noteq> d" using betweennotequal[OF `axioms` `bet C K d`] by blast
			have "col H K m" using collinearorder[OF `axioms` `col K H m`] by blast
			have "bet H m K" using collinearbetween[OF `axioms` `col f H E` `col C K d` `f \<noteq> E` `C \<noteq> d` `f \<noteq> H` `K \<noteq> d` `\<not> (meets f E C d)` `bet f m d` `col H K m`] .
			have "bet K m H" using betweennesssymmetryE[OF `axioms` `bet H m K`] .
			have "bet d m f" using betweennesssymmetryE[OF `axioms` `bet f m d`] .
			have "bet d m f \<and> bet K m H" using `bet d m f` `bet K m H` by blast
			have "cross d f K H" sorry
			have "\<not> col C K H" using NCorder[OF `axioms` `\<not> col K H C`] by blast
			have "col C K d" using col_b `axioms` `bet C K d \<and> col K H K \<and> \<not> col K H C` by blast
			have "d \<noteq> K" using inequalitysymmetric[OF `axioms` `K \<noteq> d`] .
			have "col C K K" using col_b `axioms` `K = K` by blast
			have "\<not> col d K H" using NChelper[OF `axioms` `\<not> col C K H` `col C K d` `col C K K` `d \<noteq> K`] .
			have "oppo_side d H K f" using crossimpliesopposite[OF `axioms` `cross d f K H` `\<not> col d K H`] by blast
			have "parallel A b E f" using `parallel A b E f` .
			have "parallel d C E f" using parallelflip[OF `axioms` `parallel C d E f`] by blast
			have "bet d K C" using betweennesssymmetryE[OF `axioms` `bet C K d`] .
			have "oppo_side f H K d" using oppositesidesymmetric[OF `axioms` `oppo_side d H K f`] .
			have "oppo_side A G H f" using `oppo_side A G H f` .
			have "parallel A b d C" using Prop30A[OF `axioms` `parallel A b E f` `parallel d C E f` `bet G H K` `bet A G b` `bet E H f` `bet d K C` `oppo_side A G H f` `oppo_side f H K d`] .
			have "parallel A b C d" using parallelflip[OF `axioms` `parallel A b d C`] by blast
		next
	next
		case 2
		consider "cross C f K H"|"cross C E K H" using `cross C f K H \<or> cross C E K H`  by blast
		hence parallel A b C d
		proof (cases)
			case 1
			obtain M where "bet C M f \<and> bet K M H" sorry
			have "bet C M f" using `bet C M f \<and> bet K M H` by blast
			have "bet K M H" using `bet C M f \<and> bet K M H` by blast
			have "col K M H" using col_b `axioms` `bet C M f \<and> bet K M H` by blast
			have "col K H M" using collinearorder[OF `axioms` `col K M H`] by blast
			have "bet E H f" using `bet E H f` .
			have "\<not> col K H E" using NCorder[OF `axioms` `\<not> col E H K`] by blast
			have "\<not> col K H C" using NCorder[OF `axioms` `\<not> col C K H`] by blast
			have "col K H M \<and> col K H H \<and> col K H M \<and> bet E H f \<and> bet C M f \<and> \<not> col K H E \<and> \<not> col K H C" using `col K H M` `col K H H` `col K H M` `bet E H f \<and> seg_eq H f E H` `bet C M f \<and> bet K M H` `\<not> col K H E` `\<not> col K H C` by blast
			have "same_side E C K H" sorry
			have "K = K" using equalityreflexiveE[OF `axioms`] .
			have "col K H K" using col_b `axioms` `K = K` by blast
			have "bet C K d \<and> col K H K \<and> \<not> col K H C" using `bet C K d \<and> seg_eq K d C K` `col K H K` `col K H M \<and> col K H H \<and> col K H M \<and> bet E H f \<and> bet C M f \<and> \<not> col K H E \<and> \<not> col K H C` by blast
			have "oppo_side C K H d" sorry
			have "oppo_side E K H d" using planeseparation[OF `axioms` `same_side E C K H` `oppo_side C K H d`] .
			obtain m where "bet E m d \<and> col K H m \<and> \<not> col K H E" sorry
			have "bet E m d" using `bet E m d \<and> col K H m \<and> \<not> col K H E` by blast
			have "col K H m" using `bet E m d \<and> col K H m \<and> \<not> col K H E` by blast
			have "parallel E f C d" using parallelsymmetric[OF `axioms` `parallel C d E f`] .
			have "\<not> (meets E f C d)" sorry
			have "C \<noteq> d" using `C \<noteq> d` .
			have "col E H f" using collinearorder[OF `axioms` `col E f H`] by blast
			have "col C K d" using `col C K d` .
			have "E \<noteq> f" using betweennotequal[OF `axioms` `bet E H f`] by blast
			have "E \<noteq> H" using inequalitysymmetric[OF `axioms` `H \<noteq> E`] .
			have "K \<noteq> d" using betweennotequal[OF `axioms` `bet C K d`] by blast
			have "col H K m" using collinearorder[OF `axioms` `col K H m`] by blast
			have "bet H m K" using collinearbetween[OF `axioms` `col E H f` `col C K d` `E \<noteq> f` `C \<noteq> d` `E \<noteq> H` `K \<noteq> d` `\<not> (meets E f C d)` `bet E m d` `col H K m`] .
			have "bet K m H" using betweennesssymmetryE[OF `axioms` `bet H m K`] .
			have "bet d m E" using betweennesssymmetryE[OF `axioms` `bet E m d`] .
			have "bet d m E \<and> bet K m H" using `bet d m E` `bet K m H` by blast
			have "cross d E K H" sorry
			have "\<not> col C K H" using NCorder[OF `axioms` `\<not> col K H C`] by blast
			have "col C K d" using col_b `axioms` `bet C K d \<and> col K H K \<and> \<not> col K H C` by blast
			have "d \<noteq> K" using inequalitysymmetric[OF `axioms` `K \<noteq> d`] .
			have "col C K K" using col_b `axioms` `K = K` by blast
			have "\<not> col d K H" using NChelper[OF `axioms` `\<not> col C K H` `col C K d` `col C K K` `d \<noteq> K`] .
			have "oppo_side d H K E" using crossimpliesopposite[OF `axioms` `cross d E K H` `\<not> col d K H`] by blast
			have "parallel d C f E" using parallelflip[OF `axioms` `parallel C d E f`] by blast
			have "bet d K C" using betweennesssymmetryE[OF `axioms` `bet C K d`] .
			have "oppo_side E H K d" using oppositesidesymmetric[OF `axioms` `oppo_side d H K E`] .
			have "oppo_side A G H E" using crossimpliesopposite[OF `axioms` `cross A E G H` `\<not> col A G H`] by blast
			have "parallel A b f E" using `parallel A b f E` .
			have "parallel d C f E" using `parallel d C f E` .
			have "bet f H E" using betweennesssymmetryE[OF `axioms` `bet E H f`] .
			have "bet d K C" using `bet d K C` .
			have "parallel A b d C" using Prop30A[OF `axioms` `parallel A b f E` `parallel d C f E` `bet G H K` `bet A G b` `bet f H E` `bet d K C` `oppo_side A G H E` `oppo_side E H K d`] .
			have "parallel A b C d" using parallelflip[OF `axioms` `parallel A b d C`] by blast
		next
			case 2
			have "oppo_side C H K E" using crossimpliesopposite[OF `axioms` `cross C E K H` `\<not> col C K H`] by blast
			have "oppo_side E H K C" using oppositesidesymmetric[OF `axioms` `oppo_side C H K E`] .
			have "oppo_side A G H E" using crossimpliesopposite[OF `axioms` `cross A E G H` `\<not> col A G H`] by blast
			have "parallel A b f E" using `parallel A b f E` .
			have "parallel C d f E" using `parallel C d f E` .
			have "bet C K d" using `bet C K d` .
			have "bet f H E" using betweennesssymmetryE[OF `axioms` `bet E H f`] .
			have "parallel A b C d" using Prop30A[OF `axioms` `parallel A b f E` `parallel C d f E` `bet G H K` `bet A G b` `bet f H E` `bet C K d` `oppo_side A G H E` `oppo_side E H K C`] .
		next
	next
	have "parallel A b d C" using parallelflip[OF `axioms` `parallel A b C d`] by blast
	have "col d C D" using collinearorder[OF `axioms` `col C d D`] by blast
	have "D \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> D`] .
	have "parallel A b D C" using collinearparallel[OF `axioms` `parallel A b d C` `col d C D` `D \<noteq> C`] .
	have "parallel A b C D" using parallelflip[OF `axioms` `parallel A b D C`] by blast
	have "parallel C D A b" using parallelsymmetric[OF `axioms` `parallel A b C D`] .
	have "parallel C D b A" using parallelflip[OF `axioms` `parallel C D A b`] by blast
	have "col b A B" using collinearorder[OF `axioms` `col A b B`] by blast
	have "\<not> col A B E" using parallelNC[OF `axioms` `parallel A B E F`] by blast
	have "B \<noteq> A" using NCdistinct[OF `axioms` `\<not> col A B E`] by blast
	have "parallel C D B A" using collinearparallel[OF `axioms` `parallel C D b A` `col b A B` `B \<noteq> A`] .
	have "parallel C D A B" using parallelflip[OF `axioms` `parallel C D B A`] by blast
	have "parallel A B C D" using parallelsymmetric[OF `axioms` `parallel C D A B`] .
	thus ?thesis by blast
qed

end