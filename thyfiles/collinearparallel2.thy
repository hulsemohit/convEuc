theory collinearparallel2
	imports Geometry NCdistinct collinear4 collinearorder collinearparallel inequalitysymmetric parallelNC parallelflip
begin

theorem(in euclidean_geometry) collinearparallel2:
	assumes 
		"parallel A B C D"
		"col C D E"
		"col C D F"
		"E \<noteq> F"
	shows "parallel A B E F"
proof -
	have "F \<noteq> E" using inequalitysymmetric[OF `E \<noteq> F`] .
	have "\<not> col A C D" using parallelNC[OF `parallel A B C D`] by blast
	have "C \<noteq> D" using NCdistinct[OF `\<not> col A C D`] by blast
	have "D \<noteq> C" using inequalitysymmetric[OF `C \<noteq> D`] .
	have "col D C E" using collinearorder[OF `col C D E`] by blast
	have "col D C F" using collinearorder[OF `col C D F`] by blast
	have "col C E F" using collinear4[OF `col D C E` `col D C F` `D \<noteq> C`] .
	consider "E = D"|"E \<noteq> D" by blast
	hence "parallel A B E F"
	proof (cases)
		assume "E = D"
		have "D \<noteq> F" using `E \<noteq> F` `E = D` by blast
		have "F \<noteq> D" using inequalitysymmetric[OF `D \<noteq> F`] .
		have "parallel A B C D" using `parallel A B C D` .
		have "parallel A B F D" using collinearparallel[OF `parallel A B C D` `col C D F` `F \<noteq> D`] .
		have "parallel A B D F" using parallelflip[OF `parallel A B F D`] by blast
		have "col C F D" using collinearorder[OF `col C D F`] by blast
		have "col C F E" using collinearorder[OF `col C E F`] by blast
		consider "C = F"|"C \<noteq> F" by blast
		hence "col F D E"
		proof (cases)
			assume "C = F"
			have "col C D E" using collinearorder[OF `col D C E`] by blast
			have "col F D E" using `col C D E` `C = F` by blast
			thus ?thesis by blast
		next
			assume "C \<noteq> F"
			have "col F D E" using collinear4[OF `col C F D` `col C F E` `C \<noteq> F`] .
			thus ?thesis by blast
		qed
		have "col D F E" using collinearorder[OF `col F D E`] by blast
		have "parallel A B E F" using collinearparallel[OF `parallel A B D F` `col D F E` `E \<noteq> F`] .
		thus ?thesis by blast
	next
		assume "E \<noteq> D"
		have "parallel A B C D" using `parallel A B C D` .
		have "parallel A B E D" using collinearparallel[OF `parallel A B C D` `col C D E` `E \<noteq> D`] .
		have "parallel A B D E" using parallelflip[OF `parallel A B E D`] by blast
		have "col D E F" using collinear4[OF `col C D E` `col C D F` `C \<noteq> D`] .
		have "parallel A B F E" using collinearparallel[OF `parallel A B D E` `col D E F` `F \<noteq> E`] .
		have "parallel A B E F" using parallelflip[OF `parallel A B F E`] by blast
		thus ?thesis by blast
	qed
	thus ?thesis by blast
qed

end