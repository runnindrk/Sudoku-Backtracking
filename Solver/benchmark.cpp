#include "sudoku_solver.cpp"
#include <iostream>
#include <fstream>
#include <string>
#include <chrono>

// -----------------------------------------------------------

void benchmark()
{
    int num_puzzles_solved = 0;
    float avg_number_guesses = 0;
    string sudoku;
    ifstream file("../Data_Sets/puzzles5_forum_hardest_1905_11+");

    if (!file.is_open()) 
        cerr << "Failed to open the file.\n";

    getline(file, sudoku);
    getline(file, sudoku);

    auto start = chrono::high_resolution_clock::now();

    while (getline(file, sudoku))
    {
        solveSudoku solve(sudoku);
        solve.backTrackingSolver();
        avg_number_guesses += static_cast<float>(solve.num_guesses - avg_number_guesses)/(num_puzzles_solved + 1.0);
        num_puzzles_solved += 1; 
        cout << num_puzzles_solved << " " << sudoku << " " << solve.num_backtrack_calls << " " << solve.num_guesses << "\n";
    }

    auto end = chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start); 

    file.close();

    cout << "\n";
    cout << num_puzzles_solved << " Solved Puzzles\n";
    cout << static_cast<float>(num_puzzles_solved)/(duration.count()*1e-6) << " Puzzles/s\n";
    cout << avg_number_guesses << " Guesses/Puzzle\n";
}

int main()
{
    /*
    string sudoku_string = "6..3.2....4.....8..........7.26............543.........8.15........8.2........7..";
    solveSudoku solve(sudoku_string);
    solve.printArrayOnTerminal(solve.sudoku);
    solve.backTrackingSolver();
    solve.printArrayOnTerminal(solve.sudoku_solution);
    cout << "\n" << solve.num_backtrack_calls << " " << solve.num_guesses << "\n";
    */

    benchmark();
    return 0;
}
