theory squarerectangle
	imports Geometry PGrectangle squareparallelogram
begin

theorem(in euclidean_geometry) squarerectangle:
	assumes 
		"square A B C D"
	shows "rectangle A B C D"
proof -
	have "parallelogram A B C D" using squareparallelogram[OF `square A B C D`] .
	have "ang_right D A B" using square_f[OF `square A B C D`] by blast
	have "rectangle A B C D" using PGrectangle[OF `parallelogram A B C D` `ang_right D A B`] .
	thus ?thesis by blast
qed

end