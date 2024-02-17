#include <algorithm>
#include <iostream>
#include <cstring>
#include <vector>
#include <map>
#include <set>

#define NUM_ROWS 9
#define NUM_COLS 9
#define SIZE_BLOCKS 3
#define POSSIBLE 1
#define IMPOSSIBLE 0
#define NUMBER_OF_PEERS 20
#define ALL_BITS 511
#define FILLED (NUM_ROWS + 1)
#define MAKE_MOVE 1
#define UNDO_MOVE 0

using namespace std;

// -----------------------------------------------------------

class readInput
{
    public:

    void printStringOnTerminal(string &sudoku_string)
    {
        string divisionBar = " _________________________\n";
        string emptySpace = " ";
        string stringValue = " ";
        bool flagRow = false;

        for (int i = 0; i < NUM_COLS; i++)
        {
            flagRow = false;

            for (int j = 0; j < NUM_ROWS; j++)
            {
                stringValue = sudoku_string[i*NUM_COLS + j];

                if (!(i%SIZE_BLOCKS) and !flagRow)
                {
                    cout << divisionBar;
                    flagRow = true;
                }

                if (!(j%SIZE_BLOCKS))
                    cout << " |";

                if (stringValue != ".")
                    cout << emptySpace + stringValue; 

                else
                    cout << emptySpace + emptySpace;    
            }

            cout << " |\n";
        }

        cout << divisionBar;
    }

    void printArrayOnTerminal(int (&sudoku)[NUM_ROWS][NUM_COLS])
    {
        string divisionBar = " _________________________\n";
        string emptySpace = " ";
        string stringValue = " ";
        bool flagRow = false;

        for (int i = 0; i < NUM_COLS; i++)
        {
            flagRow = false;

            for (int j = 0; j < NUM_ROWS; j++)
            {
                stringValue = to_string(sudoku[i][j]);

                if (!(i%SIZE_BLOCKS) and !flagRow)
                {
                    cout << divisionBar;
                    flagRow = true;
                }

                if (!(j%SIZE_BLOCKS))
                    cout << " |";

                if (stringValue != "0")
                    cout << emptySpace + stringValue; 

                else
                    cout << emptySpace + emptySpace;    
            }

            cout << " |\n";
        }

        cout << divisionBar;
    }

    void fillInternalRepresentation(string &sudoku_string, int (&sudoku)[NUM_ROWS][NUM_COLS])
    {
        string stringValue;

        for (int i = 0; i < NUM_COLS; i++)
            for (int j = 0; j < NUM_ROWS; j++)
            {
                stringValue = sudoku_string[i*NUM_COLS + j];

                if (stringValue != ".")
                    sudoku[i][j] = stoi(stringValue);

                else 
                    sudoku[i][j] = 0;
            }
    }
};

// -----------------------------------------------------------

class solveSudoku : public readInput
{
    public:

    int number_of_clues     = 0;
    int num_backtrack_calls = 0;
    int num_guesses         = 0;

    int sudoku[NUM_ROWS][NUM_COLS]          = {0};
    int sudoku_solution[NUM_ROWS][NUM_COLS] = {0};
    int possible_values[NUM_ROWS][NUM_COLS] = {0};

    map<array<int, 2>, array<array<int, 2>, NUMBER_OF_PEERS>> cell_peers;
    map<int, array<array<int, 2>, NUM_ROWS>>                        rows;
    map<int, array<array<int, 2>, NUM_COLS>>                    collumns;
    map<int, array<array<int, 2>, SIZE_BLOCKS*SIZE_BLOCKS>>       blocks;

    // -------------------------------------------------------
    // initilization

    solveSudoku(string &sudoku_string)
    
    {
        fillInternalRepresentation(sudoku_string, sudoku);
        fillInternalRepresentation(sudoku_string, sudoku_solution);
        numberOfClues();
        fillCellPeers();
        setAllPossileValues();
    }

    // -------------------------------------------------------
    // preparing the machinery

    set<array<int, 2>> findCellPeers(int col, int row)
    {
        int row_block = row/SIZE_BLOCKS;
        int col_block = col/SIZE_BLOCKS;
        set<array<int, 2>> peers;

        for (int i = 0; i < NUM_ROWS; i++)
            peers.insert({col, i});

        for (int i = 0; i < NUM_COLS; i++)
            peers.insert({i, row});

        for (int i = 0; i < SIZE_BLOCKS; i++)
            for (int j = 0; j < SIZE_BLOCKS; j++)
                peers.insert({col_block*SIZE_BLOCKS + i, row_block*SIZE_BLOCKS + j});

        peers.erase({col, row});

        return peers;         
    }

    void fillCellPeers()
    {
        array<array<int, 2>, NUMBER_OF_PEERS> peers_array;

        for (int i = 0; i < NUM_COLS; i++)
            for (int j = 0; j < NUM_ROWS; j++)
            {
                set<array<int, 2>> peers = findCellPeers(i, j);
                auto it = peers.begin();

                for (int i = 0; i < peers.size(); ++i)
                {
                    peers_array[i] = *it;
                    ++it;
                }

                cell_peers[{i, j}] = peers_array;
            }
    }

    void setCellPossibleValues(int col, int row)
    {
        array<array<int, 2>, NUMBER_OF_PEERS> peers = cell_peers.find({col, row})->second;
        int base_value = 1;
        int all_values = 0;
        int peer_value = ALL_BITS;

        for (int i = 0; i < NUMBER_OF_PEERS; i++)
        {
            int cell_value = sudoku[peers[i][0]][peers[i][1]];

            if (cell_value)
            {
                all_values = all_values | (base_value <<= (cell_value - 1));
                base_value = 1;
            }
        }

        possible_values[col][row] = peer_value ^ all_values;;
    }

    void setAllPossileValues()
    {
        for (int i = 0; i < NUM_COLS; i++)
            for (int j = 0; j < NUM_ROWS; j++)
                if (!sudoku[i][j])
                    setCellPossibleValues(i, j);
    }

    int countSetBits(int n)
    {
        int count = 0;

        while (n) 
        {
            count += n & 1;
            n >>= 1;
        }

        return count;
    }

    bool isPowerOfTwo(int n) 
    {
        return ((n & (n - 1)) == 0);
    }

    void numberOfClues()
    {
        for (int i = 0; i < NUM_COLS; i++)
            for (int j = 0; j < NUM_ROWS; j++)
                if (sudoku[i][j])
                    number_of_clues += 1;
    }

    // -------------------------------------------------------
    // backtracking methods

    void moveMakeUndo(int col, int row, int value, int undo_make)
    {
        array<array<int, 2>, NUMBER_OF_PEERS> peers = cell_peers.find({col, row})->second;

        if (undo_make)
        {
            int base = 1;
            int A = (base <<= (value - 1));
            sudoku[col][row] = value;

            for (int i = 0; i < NUMBER_OF_PEERS; i++)
                if (!sudoku[peers[i][0]][peers[i][1]])
                {
                    int B = possible_values[peers[i][0]][peers[i][1]];
                    possible_values[peers[i][0]][peers[i][1]] = (~A) & B;
                }

            /*sudoku[col][row] = value;

            for (int i = 0; i < NUMBER_OF_PEERS; i++)
                if (!sudoku[peers[i][0]][peers[i][1]])
                    setCellPossibleValues(peers[i][0], peers[i][1]);*/
        }

        else
        {
            sudoku[col][row] = 0;

            /*for (int i = 0; i < NUMBER_OF_PEERS; i++)
                if (!sudoku[peers[i][0]][peers[i][1]])
                    setCellPossibleValues(peers[i][0], peers[i][1]);*/
        }
    }

    int checkValid()
    {
        for (int i = 0; i < NUM_COLS; i++)
            for (int j = 0; j < NUM_ROWS; j++)
                if (!sudoku[i][j] && !possible_values[i][j])
                    return IMPOSSIBLE;

        return POSSIBLE;
    }

    int findLeastBranchingCell()
    {
        vector<int> branching(NUM_ROWS*NUM_COLS);

        for (int i = 0; i < NUM_COLS; i++)
            for (int j = 0; j < NUM_ROWS; j++)
            {
                if (sudoku[i][j])
                    branching[i*NUM_COLS + j] = FILLED;

                else
                    branching[i*NUM_COLS + j] = countSetBits(possible_values[i][j]);
            }

        auto min_iterator = min_element(branching.begin(), branching.end());
        int min_index = min_iterator - branching.begin();

        return min_index;
    }

    // -------------------------------------------------------
    // backtracking solver

    int backTrackingSolver(int depth = 0)
    {
        if (depth == NUM_COLS*NUM_ROWS - number_of_clues)
        {
            memcpy(sudoku_solution, sudoku, sizeof(sudoku));
            return 0;
        }
        
        else
        {
            num_backtrack_calls += 1;
            int next_cell = findLeastBranchingCell();
            int col = next_cell/NUM_COLS;
            int row = next_cell%NUM_ROWS;
            int current_value = possible_values[col][row];
            
            /*cout << num_backtrack_calls << "\n";
            printArrayOnTerminal(sudoku);

            for (int i = 0; i < NUM_COLS; i++)
                for (int j = 0; j < NUM_ROWS; j++)
                    cout << i << " " << j << " " << possible_values[i][j] << "\n";*/
            
            for (int i = 0; i < NUM_ROWS; i++)
            {
                int valid = 1;
                int try_value = i + 1;
                int base_value = 1;

                if (!current_value)
                    continue;

                if (!(current_value & (base_value <<= i)))
                    continue;

                if (!isPowerOfTwo(current_value))
                    num_guesses += 1;

                int possible_values_temp[NUM_ROWS][NUM_COLS];
                memcpy(possible_values_temp, possible_values, sizeof(possible_values));

                moveMakeUndo(col, row, try_value, MAKE_MOVE);
                backTrackingSolver(depth + 1);
                
                moveMakeUndo(col, row, try_value, UNDO_MOVE);
                memcpy(possible_values, possible_values_temp, sizeof(possible_values));
            }

            return 0;
        }
    }
};