import javax.swing.*;
import javax.swing.Timer;
import javax.swing.border.EmptyBorder;
import javax.swing.border.MatteBorder;
import java.awt.*;
import java.awt.event.*;
import java.io.*;
import java.text.SimpleDateFormat;
import java.util.*;
import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.TimeUnit;

public class game_panel extends JLayeredPane {
    //bugs founded in game
    //one click without any wall suggestion then press enter and one border without wall will appear in illegal location
    //map info is something useless when we have original map itself
    //agent build useless qouridors
    //agent trapped in some situations! and move both sides repeatedly
    private static Player[] game_players;                                           //player objects
    private static Integer game_turn;                                               //current selected walls for keyboard listener
    private static Map game_map;
    private static int tile_width, tile_height, h_wall_height, v_wall_width;
    private static int user_num = 0;
    private static Component last_clicked_element;
    private static Integer[][] node_pool;
    private static final Color Tile_Color = new Color(0x0E1435);
    private static final Color Tile_back_Color = new Color(39, 51, 75);
    private static final Color square_Color = new Color(0x00073E);
    private static final Color h_wall_Color = new Color(0x294F47);
    private static final Color v_wall_Color = new Color(0x294F47);
    private static JPanel game_screen;
    private static HashMap<m_info, byte[]>[][][] memoize;//first address second distances for each player
    private static HashMap<m_info, Double>[][][][][] tree_memo;
    private static final int MAX_TREE_HEU_DEPTH = 10;
    private static final int MAP_SIZE = 81;
    //learning variables
    //index of array : game turns, opponent distance, winner walked distance, opponent walked distance
    private static double[] score_policy = new double[]{-1.0, 1.75, -0.5, 2.5};
    private static boolean training_mode = true;
    private static Random random = new Random();
    private static double[][] current_generation = new double[][]{{2.5802125588643507,2.324098916199723, 2.5}, {2.5802125588643507,2.324098916199723, 2.5}};
    private static double[][] mating_pool = new double[10][3];
    private static int process_meter = 0;
    private static int winner = -1;
    private static int generation_num = 1;
    private static int current_pair;
    private static boolean save_depth_0 = true;
    private static long calculated = 0L;
    private static double evaluate_quality() {
        return score_policy[0] * game_turn + score_policy[1] * check_block_player(1 - winner) + score_policy[2] * game_players[winner].walked_distance + score_policy[3] * game_players[1 - winner].walked_distance;
    }
    private static double cross_over(double parent1,double parent2){
        double alpha = random.nextGaussian();
        return parent1 * alpha + parent2 * (1 - alpha);
    }
    private static void mutation(double[] gene){
        double r_value = random.nextGaussian();
        double mutation_prob = 0.1;
        if (r_value < mutation_prob) {
            double mutation_rate = 0.1;
            gene[0] += (random.nextInt() % 2 == 0 ? +1 : -1) * mutation_rate * random.nextGaussian();
            gene[1] += (random.nextInt() % 2 == 0 ? +1 : -1) * mutation_rate * random.nextGaussian();
        }
    }
    private static void manage_genetic_process(){
        //first of process : logging information and generating new children
        if (process_meter == 0) {
            //create new set of children
            mating_pool = new double[10][3];
            for (int i = 0; i < mating_pool.length; i++) {
                mating_pool[i][0] = cross_over(current_generation[0][0], current_generation[1][0]);
                mating_pool[i][1] = cross_over(current_generation[0][1], current_generation[1][1]);
                mutation(mating_pool[i]);
            }
            //reset genetic variables
            current_pair = 2;
            //set new evaluate new children
            current_generation[0] = mating_pool[0];
            current_generation[1] = mating_pool[1];
            //ready to begin next process
            process_meter += 1;
        }
        //found value of children
        else if (process_meter >= 1 && process_meter <= 4) {
            //process winner data
            mating_pool[current_pair - 2 + winner][2] = evaluate_quality();
            mating_pool[current_pair - 2 + 1 - winner][2] = -10000.0;
            //do process
            current_generation[0] = mating_pool[current_pair];
            current_generation[1] = mating_pool[current_pair+1];
            current_pair += 2;
            //proceed to next phase
            process_meter += 1;
        }
        //find next generation
        else if (process_meter == 5) {
            //process winner data
            mating_pool[current_pair - 2 + winner][2] = evaluate_quality();
            mating_pool[current_pair - 2 + 1 - winner][2] = -1.0;
            //sort the array
            Arrays.sort(mating_pool, (o1, o2) -> -Double.compare(o1[2],o2[2]));
            //selecting two child!
            int selected = 0;
            int index = 0;
            while (selected != 2) {
                if (random.nextDouble() < (5.0 - index) / 15.0) {
                    current_generation[selected] = mating_pool[index];
                    selected += 1;
                }
                index += 1;
                if(index == 4) index = 0;
            }
            //saving new findings!
            try {
                SimpleDateFormat formatter= new SimpleDateFormat("yyyy-MM-dd 'at' HH:mm:ss z");
                SimpleDateFormat formatter1= new SimpleDateFormat("yyyy-MM-dd----HH;mm;ss");
                Date date = new Date(System.currentTimeMillis());
                PrintWriter writer = new PrintWriter(".\\log\\" + generation_num + "gene_log" + formatter1.format(date) + ".dat");
                writer.print("Date of generation : ");
                writer.println(formatter.format(date));
                writer.println("Game turns : " + game_turn);
                writer.println("Generation data : ");
                for (int i = 0; i < 10; i++) {
                    writer.println("gene<"+i+">:"+mating_pool[i][0]+":"+mating_pool[i][1]+":"+mating_pool[i][2]);
                }
                writer.println("Selected children : ");
                for (int i = 0; i < 2; i++) {
                    writer.println(">>" + current_generation[i][0] + "," + current_generation[i][1]);
                }
                writer.println("eof.");
                writer.close();
            } catch (FileNotFoundException e) {
                e.printStackTrace();
            }
            process_meter = 0;
            generation_num++;
        }
    }
    private static int row(int location,int num){
        return location / num;
    }
    private static int col(int location,int num){
        return location % num;
    }
    private void mods(int d,int k,boolean add,int builder){
        if (add) {
            if (d == 0) {
                add_wall_inline(TYPE.HORIZONTAL,row(k,8),col(k,8),true);
            } else {
                add_wall_inline(TYPE.VERTICAL,row(k,8),col(k,8),true);
            }
            game_players[builder].p_cor -= 1;
        }else{
            if (d == 0) {
                add_wall_inline(TYPE.HORIZONTAL,row(k,8),col(k,8),false);
            } else {
                add_wall_inline(TYPE.VERTICAL,row(k,8),col(k,8),false);
            }
            game_players[builder].p_cor += 1;
        }
    }

    //building data base
    private void data_base_builder(int final_depth) {
        boolean[] blocks_in_game = new boolean[20];
        GameTree exprement_tree;
        int game_tile = 81;
        int game_square = 64;
        //first we will calculate all leaves
        //then calculate all depth 1 trees
        //then calculate all depth 2 trees and so on

        for (int tree_depth = 1; tree_depth <= final_depth; tree_depth++) {
            for (int e = 0; e < 20; e++) {
                blocks_in_game[e] = true;
                System.out.println("finding data for depth of " + tree_depth);
                //player 1 locations
                for (int i = 0; i < game_tile; i++) {
                    //player 2 locations
                    for (int j = 0; j < game_tile; j++) {
                        if (i != 44 && j != 36) {
                            //choose player
                            for (int t = 0; t < 2; t++) {
                                //player 1 != player 2 : there is no symmetry
                                if (i != j) {
                                    //valid data to enter
                                    //TODO FIRST LOCATION DATA
                                    int first_row_p1 = game_players[0].p_r;
                                    int first_row_p2 = game_players[1].p_r;
                                    int first_col_p1 = game_players[0].p_c;
                                    int first_col_p2 = game_players[1].p_c;
                                    //TODO MOVE PLAYERS
                                    move_player_inline(first_row_p1, first_col_p1, row(i, 9), col(i, 9), 0);
                                    move_player_inline(first_row_p2, first_col_p2, row(j, 9), col(j, 9), 1);
                                    //TODO ADDING BLOCKS IN THE MAP
                                    if (blocks_in_game[0]) for (int k0 = 0; k0 < game_square; k0++) {
                                        for (int d0 = 0; d0 < 2; d0++) {
                                            //TODO CHOOSE PLAYER WHO BUILD BLOCK
                                            for (int p0 = 0; p0 < 2; p0++) {
                                                //TODO ADD BLOCK HERE
                                                mods(d0, k0, true, p0);
                                                //TODO BEGIN OF NEW LEVEL
                                                if (blocks_in_game[1]) for (int k1 = k0 + 1; k1 < game_square; k1++) {
                                                    for (int d1 = 0; d1 < 2; d1++) {
                                                        //TODO CHOOSE PLAYER WHO BUILD BLOCK
                                                        for (int p1 = 0; p1 < 2; p1++) {
                                                            //TODO ADD BLOCK HERE
                                                            mods(d1, k1, true, p1);
                                                            //TODO BEGIN OF NEW LEVEL
                                                            if (blocks_in_game[2])
                                                                for (int k2 = k1 + 1; k2 < game_square; k2++) {
                                                                    for (int d2 = 0; d2 < 2; d2++) {
                                                                        //TODO CHOOSE PLAYER WHO BUILD BLOCK
                                                                        for (int p2 = 0; p2 < 2; p2++) {
                                                                            //TODO ADD BLOCK HERE
                                                                            mods(d2, k2, true, p2);
                                                                            //TODO BEGIN OF NEW LEVEL
                                                                            if (blocks_in_game[3])
                                                                                for (int k3 = k2 + 1; k3 < game_square; k3++) {
                                                                                    for (int d3 = 0; d3 < 2; d3++) {
                                                                                        //TODO CHOOSE PLAYER WHO BUILD BLOCK
                                                                                        for (int p3 = 0; p3 < 2; p3++) {
                                                                                            //TODO ADD BLOCK HERE
                                                                                            mods(d3, k3, true, p3);
                                                                                            //TODO BEGIN OF NEW LEVEL
                                                                                            if (blocks_in_game[4])
                                                                                                for (int k4 = k3 + 1; k4 < game_square; k4++) {
                                                                                                    for (int d4 = 0; d4 < 2; d4++) {
                                                                                                        //TODO CHOOSE PLAYER WHO BUILD BLOCK
                                                                                                        for (int p4 = 0; p4 < 2; p4++) {
                                                                                                            //TODO ADD BLOCK HERE
                                                                                                            mods(d4, k4, true, p4);
                                                                                                            //TODO BEGIN OF NEW LEVEL
                                                                                                            if (blocks_in_game[5])
                                                                                                                for (int k5 = k4 + 1; k5 < game_square; k5++) {
                                                                                                                    for (int d5 = 0; d5 < 2; d5++) {
                                                                                                                        //TODO CHOOSE PLAYER WHO BUILD BLOCK
                                                                                                                        for (int p5 = 0; p5 < 2; p5++) {
                                                                                                                            //TODO ADD BLOCK HERE
                                                                                                                            mods(d5, k5, true, p5);
                                                                                                                            //TODO BEGIN OF NEW LEVEL
                                                                                                                            if (blocks_in_game[6])
                                                                                                                                for (int k6 = k5 + 1; k6 < game_square; k6++) {
                                                                                                                                    for (int d6 = 0; d6 < 2; d6++) {
                                                                                                                                        //TODO CHOOSE PLAYER WHO BUILD BLOCK
                                                                                                                                        for (int p6 = 0; p6 < 2; p6++) {
                                                                                                                                            //TODO ADD BLOCK HERE
                                                                                                                                            mods(d6, k6, true, p6);
                                                                                                                                            //TODO BEGIN OF NEW LEVEL
                                                                                                                                            if (blocks_in_game[7])
                                                                                                                                                for (int k7 = k6 + 1; k7 < game_square; k7++) {
                                                                                                                                                    for (int d7 = 0; d7 < 2; d7++) {
                                                                                                                                                        //TODO CHOOSE PLAYER WHO BUILD BLOCK
                                                                                                                                                        for (int p7 = 0; p7 < 2; p7++) {
                                                                                                                                                            //TODO ADD BLOCK HERE
                                                                                                                                                            mods(d7, k7, true, p7);
                                                                                                                                                            //TODO BEGIN OF NEW LEVEL
                                                                                                                                                            if (blocks_in_game[8])
                                                                                                                                                                for (int k8 = k7 + 1; k8 < game_square; k8++) {
                                                                                                                                                                    for (int d8 = 0; d8 < 2; d8++) {
                                                                                                                                                                        //TODO CHOOSE PLAYER WHO BUILD BLOCK
                                                                                                                                                                        for (int p8 = 0; p8 < 2; p8++) {
                                                                                                                                                                            //TODO ADD BLOCK HERE
                                                                                                                                                                            mods(d8, k8, true, p8);
                                                                                                                                                                            //TODO BEGIN OF NEW LEVEL
                                                                                                                                                                            if (blocks_in_game[9])
                                                                                                                                                                                for (int k9 = k8 + 1; k9 < game_square; k9++) {
                                                                                                                                                                                    for (int d9 = 0; d9 < 2; d9++) {
                                                                                                                                                                                        //TODO CHOOSE PLAYER WHO BUILD BLOCK
                                                                                                                                                                                        for (int p9 = 0; p9 < 2; p9++) {
                                                                                                                                                                                            //TODO ADD BLOCK HERE
                                                                                                                                                                                            mods(d9, k9, true, p9);
                                                                                                                                                                                            //TODO BEGIN OF NEW LEVEL
                                                                                                                                                                                            if (blocks_in_game[10])
                                                                                                                                                                                                for (int k10 = k9 + 1; k10 < game_square; k10++) {
                                                                                                                                                                                                    for (int d10 = 0; d10 < 2; d10++) {
                                                                                                                                                                                                        //TODO CHOOSE PLAYER WHO BUILD BLOCK
                                                                                                                                                                                                        for (int p10 = 0; p10 < 2; p10++) {
                                                                                                                                                                                                            //TODO ADD BLOCK HERE
                                                                                                                                                                                                            mods(d10, k10, true, p10);
                                                                                                                                                                                                            //TODO BEGIN OF NEW LEVEL
                                                                                                                                                                                                            if (blocks_in_game[11])
                                                                                                                                                                                                                for (int k11 = k10 + 1; k11 < game_square; k11++) {
                                                                                                                                                                                                                    for (int d11 = 0; d11 < 2; d11++) {
                                                                                                                                                                                                                        //TODO CHOOSE PLAYER WHO BUILD BLOCK
                                                                                                                                                                                                                        for (int p11 = 0; p11 < 2; p11++) {
                                                                                                                                                                                                                            //TODO ADD BLOCK HERE
                                                                                                                                                                                                                            mods(d11, k11, true, p11);
                                                                                                                                                                                                                            //TODO BEGIN OF NEW LEVEL
                                                                                                                                                                                                                            if (blocks_in_game[12])
                                                                                                                                                                                                                                for (int k12 = k11 + 1; k12 < game_square; k12++) {
                                                                                                                                                                                                                                    for (int d12 = 0; d12 < 2; d12++) {
                                                                                                                                                                                                                                        //TODO CHOOSE PLAYER WHO BUILD BLOCK
                                                                                                                                                                                                                                        for (int p12 = 0; p12 < 2; p12++) {
                                                                                                                                                                                                                                            //TODO ADD BLOCK HERE
                                                                                                                                                                                                                                            mods(d12, k12, true, p12);
                                                                                                                                                                                                                                            //TODO BEGIN OF NEW LEVEL
                                                                                                                                                                                                                                            if (blocks_in_game[13])
                                                                                                                                                                                                                                                for (int k13 = k12 + 1; k13 < game_square; k13++) {
                                                                                                                                                                                                                                                    for (int d13 = 0; d13 < 2; d13++) {
                                                                                                                                                                                                                                                        //TODO CHOOSE PLAYER WHO BUILD BLOCK
                                                                                                                                                                                                                                                        for (int p13 = 0; p13 < 2; p13++) {
                                                                                                                                                                                                                                                            //TODO ADD BLOCK HERE
                                                                                                                                                                                                                                                            mods(d13, k13, true, p13);
                                                                                                                                                                                                                                                            //TODO BEGIN OF NEW LEVEL
                                                                                                                                                                                                                                                            if (blocks_in_game[14])
                                                                                                                                                                                                                                                                for (int k14 = k13 + 1; k14 < game_square; k14++) {
                                                                                                                                                                                                                                                                    for (int d14 = 0; d14 < 2; d14++) {
                                                                                                                                                                                                                                                                        //TODO CHOOSE PLAYER WHO BUILD BLOCK
                                                                                                                                                                                                                                                                        for (int p14 = 0; p14 < 2; p14++) {
                                                                                                                                                                                                                                                                            //TODO ADD BLOCK HERE
                                                                                                                                                                                                                                                                            mods(d14, k14, true, p14);
                                                                                                                                                                                                                                                                            //TODO BEGIN OF NEW LEVEL
                                                                                                                                                                                                                                                                            if (blocks_in_game[15])
                                                                                                                                                                                                                                                                                for (int k15 = k14 + 1; k15 < game_square; k15++) {
                                                                                                                                                                                                                                                                                    for (int d15 = 0; d15 < 2; d15++) {
                                                                                                                                                                                                                                                                                        //TODO CHOOSE PLAYER WHO BUILD BLOCK
                                                                                                                                                                                                                                                                                        for (int p15 = 0; p15 < 2; p15++) {
                                                                                                                                                                                                                                                                                            //TODO ADD BLOCK HERE
                                                                                                                                                                                                                                                                                            mods(d15, k15, true, p15);
                                                                                                                                                                                                                                                                                            //TODO BEGIN OF NEW LEVEL
                                                                                                                                                                                                                                                                                            if (blocks_in_game[16])
                                                                                                                                                                                                                                                                                                for (int k16 = k15 + 1; k16 < game_square; k16++) {
                                                                                                                                                                                                                                                                                                    for (int d16 = 0; d16 < 2; d16++) {
                                                                                                                                                                                                                                                                                                        //TODO CHOOSE PLAYER WHO BUILD BLOCK
                                                                                                                                                                                                                                                                                                        for (int p16 = 0; p16 < 2; p16++) {
                                                                                                                                                                                                                                                                                                            //TODO ADD BLOCK HERE
                                                                                                                                                                                                                                                                                                            mods(d16, k16, true, p16);
                                                                                                                                                                                                                                                                                                            //TODO BEGIN OF NEW LEVEL
                                                                                                                                                                                                                                                                                                            if (blocks_in_game[17])
                                                                                                                                                                                                                                                                                                                for (int k17 = k16 + 1; k17 < game_square; k17++) {
                                                                                                                                                                                                                                                                                                                    for (int d17 = 0; d17 < 2; d17++) {
                                                                                                                                                                                                                                                                                                                        //TODO CHOOSE PLAYER WHO BUILD BLOCK
                                                                                                                                                                                                                                                                                                                        for (int p17 = 0; p17 < 2; p17++) {
                                                                                                                                                                                                                                                                                                                            //TODO ADD BLOCK HERE
                                                                                                                                                                                                                                                                                                                            mods(d17, k17, true, p17);
                                                                                                                                                                                                                                                                                                                            //TODO BEGIN OF NEW LEVEL
                                                                                                                                                                                                                                                                                                                            if (blocks_in_game[18])
                                                                                                                                                                                                                                                                                                                                for (int k18 = k17 + 1; k18 < game_square; k18++) {
                                                                                                                                                                                                                                                                                                                                    for (int d18 = 0; d18 < 2; d18++) {
                                                                                                                                                                                                                                                                                                                                        //TODO CHOOSE PLAYER WHO BUILD BLOCK
                                                                                                                                                                                                                                                                                                                                        for (int p18 = 0; p18 < 2; p18++) {
                                                                                                                                                                                                                                                                                                                                            //TODO ADD BLOCK HERE
                                                                                                                                                                                                                                                                                                                                            mods(d18, k18, true, p18);
                                                                                                                                                                                                                                                                                                                                            //TODO BEGIN OF NEW LEVEL
                                                                                                                                                                                                                                                                                                                                            if (blocks_in_game[19])
                                                                                                                                                                                                                                                                                                                                                for (int k19 = k18 + 1; k19 < game_square; k19++) {
                                                                                                                                                                                                                                                                                                                                                    for (int d19 = 0; d19 < 2; d19++) {
                                                                                                                                                                                                                                                                                                                                                        //TODO CHOOSE PLAYER WHO BUILD BLOCK
                                                                                                                                                                                                                                                                                                                                                        for (int p19 = 0; p19 < 2; p19++) {
                                                                                                                                                                                                                                                                                                                                                            //TODO ADD BLOCK HERE
                                                                                                                                                                                                                                                                                                                                                            mods(d19, k19, true, p19);
                                                                                                                                                                                                                                                                                                                                                            //TODO BEGIN OF NEW LEVEL
                                                                                                                                                                                                                                                                                                                                                            //NO NEW LEVEL IS POSSIBLE! :D
                                                                                                                                                                                                                                                                                                                                                            //TODO CALCULATE QUALITY HERE
                                                                                                                                                                                                                                                                                                                                                            exprement_tree = new GameTree((byte) t, (byte) tree_depth);
                                                                                                                                                                                                                                                                                                                                                            if (tree_depth != 1)
                                                                                                                                                                                                                                                                                                                                                                exprement_tree.minimax(exprement_tree.tree_root);
                                                                                                                                                                                                                                                                                                                                                            //TODO REMOVE BLOCK HERE
                                                                                                                                                                                                                                                                                                                                                            mods(d19, k19, false, p19);
                                                                                                                                                                                                                                                                                                                                                        }
                                                                                                                                                                                                                                                                                                                                                    }
                                                                                                                                                                                                                                                                                                                                                }
                                                                                                                                                                                                                                                                                                                                            //TODO CALCULATE QUALITY HERE
                                                                                                                                                                                                                                                                                                                                            exprement_tree = new GameTree((byte) t, (byte) tree_depth);
                                                                                                                                                                                                                                                                                                                                            if (tree_depth != 1)
                                                                                                                                                                                                                                                                                                                                                exprement_tree.minimax(exprement_tree.tree_root);
                                                                                                                                                                                                                                                                                                                                            //TODO REMOVE BLOCK HERE
                                                                                                                                                                                                                                                                                                                                            mods(d18, k18, false, p18);
                                                                                                                                                                                                                                                                                                                                        }
                                                                                                                                                                                                                                                                                                                                    }
                                                                                                                                                                                                                                                                                                                                }
                                                                                                                                                                                                                                                                                                                            //TODO CALCULATE QUALITY HERE
                                                                                                                                                                                                                                                                                                                            exprement_tree = new GameTree((byte) t, (byte) tree_depth);
                                                                                                                                                                                                                                                                                                                            if (tree_depth != 1)
                                                                                                                                                                                                                                                                                                                                exprement_tree.minimax(exprement_tree.tree_root);
                                                                                                                                                                                                                                                                                                                            //TODO REMOVE BLOCK HERE
                                                                                                                                                                                                                                                                                                                            mods(d17, k17, false, p17);
                                                                                                                                                                                                                                                                                                                        }
                                                                                                                                                                                                                                                                                                                    }
                                                                                                                                                                                                                                                                                                                }
                                                                                                                                                                                                                                                                                                            //TODO CALCULATE QUALITY HERE
                                                                                                                                                                                                                                                                                                            exprement_tree = new GameTree((byte) t, (byte) tree_depth);
                                                                                                                                                                                                                                                                                                            if (tree_depth != 1)
                                                                                                                                                                                                                                                                                                                exprement_tree.minimax(exprement_tree.tree_root);
                                                                                                                                                                                                                                                                                                            //TODO REMOVE BLOCK HERE
                                                                                                                                                                                                                                                                                                            mods(d16, k16, false, p16);
                                                                                                                                                                                                                                                                                                        }
                                                                                                                                                                                                                                                                                                    }
                                                                                                                                                                                                                                                                                                }
                                                                                                                                                                                                                                                                                            //TODO CALCULATE QUALITY HERE
                                                                                                                                                                                                                                                                                            exprement_tree = new GameTree((byte) t, (byte) tree_depth);
                                                                                                                                                                                                                                                                                            if (tree_depth != 1)
                                                                                                                                                                                                                                                                                                exprement_tree.minimax(exprement_tree.tree_root);
                                                                                                                                                                                                                                                                                            //TODO REMOVE BLOCK HERE
                                                                                                                                                                                                                                                                                            mods(d15, k15, false, p15);
                                                                                                                                                                                                                                                                                        }
                                                                                                                                                                                                                                                                                    }
                                                                                                                                                                                                                                                                                }
                                                                                                                                                                                                                                                                            //TODO CALCULATE QUALITY HERE
                                                                                                                                                                                                                                                                            exprement_tree = new GameTree((byte) t, (byte) tree_depth);
                                                                                                                                                                                                                                                                            if (tree_depth != 1)
                                                                                                                                                                                                                                                                                exprement_tree.minimax(exprement_tree.tree_root);
                                                                                                                                                                                                                                                                            //TODO REMOVE BLOCK HERE
                                                                                                                                                                                                                                                                            mods(d14, k14, false, p14);
                                                                                                                                                                                                                                                                        }
                                                                                                                                                                                                                                                                    }
                                                                                                                                                                                                                                                                }
                                                                                                                                                                                                                                                            //TODO CALCULATE QUALITY HERE
                                                                                                                                                                                                                                                            exprement_tree = new GameTree((byte) t, (byte) tree_depth);
                                                                                                                                                                                                                                                            if (tree_depth != 1)
                                                                                                                                                                                                                                                                exprement_tree.minimax(exprement_tree.tree_root);
                                                                                                                                                                                                                                                            //TODO REMOVE BLOCK HERE
                                                                                                                                                                                                                                                            mods(d13, k13, false, p13);
                                                                                                                                                                                                                                                        }
                                                                                                                                                                                                                                                    }
                                                                                                                                                                                                                                                }
                                                                                                                                                                                                                                            //TODO CALCULATE QUALITY HERE
                                                                                                                                                                                                                                            exprement_tree = new GameTree((byte) t, (byte) tree_depth);
                                                                                                                                                                                                                                            if (tree_depth != 1)
                                                                                                                                                                                                                                                exprement_tree.minimax(exprement_tree.tree_root);
                                                                                                                                                                                                                                            //TODO REMOVE BLOCK HERE
                                                                                                                                                                                                                                            mods(d12, k12, false, p12);
                                                                                                                                                                                                                                        }
                                                                                                                                                                                                                                    }
                                                                                                                                                                                                                                }
                                                                                                                                                                                                                            //TODO CALCULATE QUALITY HERE
                                                                                                                                                                                                                            exprement_tree = new GameTree((byte) t, (byte) tree_depth);
                                                                                                                                                                                                                            if (tree_depth != 1)
                                                                                                                                                                                                                                exprement_tree.minimax(exprement_tree.tree_root);
                                                                                                                                                                                                                            //TODO REMOVE BLOCK HERE
                                                                                                                                                                                                                            mods(d11, k11, false, p11);
                                                                                                                                                                                                                        }
                                                                                                                                                                                                                    }
                                                                                                                                                                                                                }
                                                                                                                                                                                                            //TODO CALCULATE QUALITY HERE
                                                                                                                                                                                                            exprement_tree = new GameTree((byte) t, (byte) tree_depth);
                                                                                                                                                                                                            if (tree_depth != 1)
                                                                                                                                                                                                                exprement_tree.minimax(exprement_tree.tree_root);
                                                                                                                                                                                                            //TODO REMOVE BLOCK HERE
                                                                                                                                                                                                            mods(d10, k10, false, p10);
                                                                                                                                                                                                        }
                                                                                                                                                                                                    }
                                                                                                                                                                                                }
                                                                                                                                                                                            //TODO CALCULATE QUALITY HERE
                                                                                                                                                                                            exprement_tree = new GameTree((byte) t, (byte) tree_depth);
                                                                                                                                                                                            if (tree_depth != 1)
                                                                                                                                                                                                exprement_tree.minimax(exprement_tree.tree_root);
                                                                                                                                                                                            //TODO REMOVE BLOCK HERE
                                                                                                                                                                                            mods(d9, k9, false, p9);
                                                                                                                                                                                        }
                                                                                                                                                                                    }
                                                                                                                                                                                }
                                                                                                                                                                            //TODO CALCULATE QUALITY HERE
                                                                                                                                                                            exprement_tree = new GameTree((byte) t, (byte) tree_depth);
                                                                                                                                                                            if (tree_depth != 1)
                                                                                                                                                                                exprement_tree.minimax(exprement_tree.tree_root);
                                                                                                                                                                            //TODO REMOVE BLOCK HERE
                                                                                                                                                                            mods(d8, k8, false, p8);
                                                                                                                                                                        }
                                                                                                                                                                    }
                                                                                                                                                                }
                                                                                                                                                            //TODO CALCULATE QUALITY HERE
                                                                                                                                                            exprement_tree = new GameTree((byte) t, (byte) tree_depth);
                                                                                                                                                            if (tree_depth != 1)
                                                                                                                                                                exprement_tree.minimax(exprement_tree.tree_root);
                                                                                                                                                            //TODO REMOVE BLOCK HERE
                                                                                                                                                            mods(d7, k7, false, p7);
                                                                                                                                                        }
                                                                                                                                                    }
                                                                                                                                                }
                                                                                                                                            //TODO CALCULATE QUALITY HERE
                                                                                                                                            exprement_tree = new GameTree((byte) t, (byte) tree_depth);
                                                                                                                                            if (tree_depth != 1)
                                                                                                                                                exprement_tree.minimax(exprement_tree.tree_root);
                                                                                                                                            //TODO REMOVE BLOCK HERE
                                                                                                                                            mods(d6, k6, false, p6);
                                                                                                                                        }
                                                                                                                                    }
                                                                                                                                }
                                                                                                                            //TODO CALCULATE QUALITY HERE
                                                                                                                            exprement_tree = new GameTree((byte) t, (byte) tree_depth);
                                                                                                                            if (tree_depth != 1)
                                                                                                                                exprement_tree.minimax(exprement_tree.tree_root);
                                                                                                                            //TODO REMOVE BLOCK HERE
                                                                                                                            mods(d5, k5, false, p5);
                                                                                                                        }
                                                                                                                    }
                                                                                                                }
                                                                                                            //TODO CALCULATE QUALITY HERE
                                                                                                            exprement_tree = new GameTree((byte) t, (byte) tree_depth);
                                                                                                            if (tree_depth != 1)
                                                                                                                exprement_tree.minimax(exprement_tree.tree_root);
                                                                                                            //TODO REMOVE BLOCK HERE
                                                                                                            mods(d4, k4, false, p4);
                                                                                                        }
                                                                                                    }
                                                                                                }
                                                                                            //TODO CALCULATE QUALITY HERE
                                                                                            exprement_tree = new GameTree((byte) t, (byte) tree_depth);
                                                                                            if (tree_depth != 1)
                                                                                                exprement_tree.minimax(exprement_tree.tree_root);
                                                                                            //TODO REMOVE BLOCK HERE
                                                                                            mods(d3, k3, false, p3);
                                                                                        }
                                                                                    }
                                                                                }
                                                                            //TODO CALCULATE QUALITY HERE
                                                                            exprement_tree = new GameTree((byte) t, (byte) tree_depth);
                                                                            if (tree_depth != 1)
                                                                                exprement_tree.minimax(exprement_tree.tree_root);
                                                                            //TODO REMOVE BLOCK HERE
                                                                            mods(d2, k2, false, p2);
                                                                        }
                                                                    }
                                                                }
                                                            //TODO CALCULATE QUALITY HERE
                                                            exprement_tree = new GameTree((byte) t, (byte) tree_depth);
                                                            if (tree_depth != 1)
                                                                exprement_tree.minimax(exprement_tree.tree_root);
                                                            //TODO REMOVE BLOCK HERE
                                                            mods(d1, k1, false, p1);
                                                        }
                                                    }
                                                }
                                                //TODO CALCULATE QUALITY HERE
                                                exprement_tree = new GameTree((byte) t, (byte) tree_depth);
                                                if (tree_depth != 1) exprement_tree.minimax(exprement_tree.tree_root);
                                                //TODO REMOVE BLOCK HERE
                                                mods(d0, k0, false, p0);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            if (tree_depth == 1) {
                save_leaves();
                save_depth_0 = false;
            }
        }

    }
    private static void save_leaves(){
        FileOutputStream fout;
        ObjectOutputStream oos;
        try {
            fout = new FileOutputStream(".\\data\\data-loc.dat");
            oos = new ObjectOutputStream(fout);
            oos.writeObject(memoize);
            fout.close();
            oos.close();
        } catch (IOException e) {
            System.out.println("error 504002 : can't write data to file");
        }
    }
    //create new instance if it does'nt exists already and return that
    game_panel(Integer n_game_players, JFrame parent) throws InterruptedException {
        reset_panel(n_game_players, parent);


        this.setBackground(new Color(69, 99, 131));
        this.setFocusable(true);
        this.requestFocusInWindow();

        memoize = new HashMap[MAP_SIZE][MAP_SIZE][2];
        //min=0,max=1 : depth 0->1 , 1->2
        tree_memo = new HashMap[MAP_SIZE][MAP_SIZE][2][2][MAX_TREE_HEU_DEPTH];
        load_data();

        ScheduledExecutorService executorService = Executors.newSingleThreadScheduledExecutor();
        executorService.scheduleAtFixedRate(game_panel::save_data, 10, 10, TimeUnit.MINUTES);

//        data_base_builder(5);

       if (training_mode) {
           manage_genetic_process();
       }

       next_player(0);
       Thread.sleep(50);

    }// VERIFIED WORKING CORRECTLY
    private static void prepare_snode(int last_used_node, int i, int cost, int p_r, int p_c){
        node_pool[last_used_node][0] = i;
        node_pool[last_used_node][1] = p_r;
        node_pool[last_used_node][2] = p_c;
        node_pool[last_used_node][3] = cost;
        switch (i) {
            case 0:{
                node_pool[last_used_node][4] = node_pool[last_used_node][3] + 8 - game_players[i].p_c;break;}
            case 1:{
                node_pool[last_used_node][4] = node_pool[last_used_node][3] + game_players[i].p_c;break;}
            case 2:{
                node_pool[last_used_node][4] = node_pool[last_used_node][3] + 8 - game_players[i].p_r;break;}
            case 3:{
                node_pool[last_used_node][4] = node_pool[last_used_node][3] + game_players[i].p_r;break;}
        }
    }
    private boolean check_block_group(){
        for (int i = 0; i < game_players.length; i++) {
            if (check_block_player(i) == -1) {
                return false;
            }
        }
        return true;
    }
    //basic blocks for storing game data in files
    class m_info implements Serializable{
        public static final long serialVersionUID = 666L;
        long v_struct,h_struct;
        m_info(long v_struct, long h_struct) {
            this.v_struct = v_struct;
            this.h_struct = h_struct;
        }
        @Override
        public int hashCode() {
            return (int) (v_struct ^ v_struct >> 32 ^ h_struct ^ h_struct >> 32);
        }

        @Override
        public boolean equals(Object obj) {
            if (obj instanceof m_info) {
                m_info ob = (m_info) obj;
                return v_struct == ob.v_struct && h_struct == ob.h_struct;
            }
            return false;
        }
    }
    //load memo map if exists or create new one
    private void load_data(){
        FileInputStream fileIn;
        ObjectInputStream objectIn;
        try {
            fileIn = new FileInputStream(".\\data\\data-loc.dat");
            objectIn = new ObjectInputStream(fileIn);
            memoize = (HashMap<m_info, byte[]>[][][]) objectIn.readObject();
            fileIn.close();
            objectIn.close();
        } catch (IOException | ClassNotFoundException e) {
            memoize = new HashMap[MAP_SIZE][MAP_SIZE][2];
            for (int i = 0; i < MAP_SIZE; i++) {
                for (int j = 0; j < MAP_SIZE; j++) {
                    for (int k = 0; k < 2; k++) {
                        memoize[i][j][k] = new HashMap<>();
                    }
                }
            }
            System.out.println("error 504001 : file not find!");
        }
        try {
            fileIn = new FileInputStream(".\\data\\data-val.dat");
            objectIn = new ObjectInputStream(fileIn);
            tree_memo= (HashMap<m_info, Double>[][][][][]) objectIn.readObject();
            fileIn.close();
            objectIn.close();
        } catch (IOException | ClassNotFoundException e) {
            tree_memo= new HashMap[MAP_SIZE][MAP_SIZE][2][2][MAX_TREE_HEU_DEPTH];
            for (int i = 0; i < MAP_SIZE; i++) {
                for (int j = 0; j < MAP_SIZE; j++) {
                    for (int k = 0; k < 2; k++) {
                        for (int l = 0; l < 2; l++) {
                            for (int m = 0; m < MAX_TREE_HEU_DEPTH; m++) {
                                tree_memo[i][j][k][l][m] = new HashMap<>();
                            }
                        }
                    }
                }
            }
            System.out.println("error 504001 : file not find!");
        }

    }
    //save memo map after using it
    private static void save_data(){
        FileOutputStream fout;
        ObjectOutputStream oos;
//        try {
//            fout = new FileOutputStream(".\\data\\data-loc.dat");
//            oos = new ObjectOutputStream(fout);
//            oos.writeObject(memoize);
//            fout.close();
//            oos.close();
//        } catch (IOException e) {
//            System.out.println("error 504002 : can't write data to file");
//        }
        try {
            fout = new FileOutputStream(".\\data\\data-val.dat");
            oos = new ObjectOutputStream(fout);
            oos.writeObject(tree_memo);
            fout.close();
            oos.close();
        } catch (IOException e) {
            System.out.println("error 504002 : can't write data to file");
        }
        if (save_depth_0) {
            save_leaves();
        }
    }
    //game functions for checking if block is legal to insert to map
    private static int check_block_player(int player) {

        PriorityQueue<Integer> bfs_queue = new PriorityQueue<>(Comparator.comparingInt(o -> node_pool[o][4]));
        int last_used_node = 0;
        boolean[][] map_info = new boolean[game_panel.game_map.map_tiles.length][game_panel.game_map.map_tiles[0].length];

        for (boolean[] booleans : map_info) Arrays.fill(booleans, false);

        int answer = -1;
        Integer[] cn;

        prepare_snode(last_used_node, player, 0, game_players[player].p_r, game_players[player].p_c);
        bfs_queue.add(last_used_node);
        last_used_node++;

        while (!bfs_queue.isEmpty()) {
            cn = node_pool[bfs_queue.poll()];
            map_info[cn[1]][cn[2]] = true;

            if ((player == 0 && cn[2] == game_map.map_tiles[0].length - 1)
                    || (player == 1 && cn[2] == 0)
                    || (player == 2 && cn[1] == game_map.map_tiles.length - 1)
                    || (player == 3 && cn[1] == 0)) {
                answer = cn[3];
                break;
            }

            //right expansion
            if (cn[2] < game_panel.game_map.map_tiles[0].length - 1 && !map_info[cn[1]][cn[2] + 1] && game_map.map_v_walls[cn[1]][cn[2]].isEnabled()) {
                prepare_snode(last_used_node, player, cn[3] + 1, cn[1], cn[2] + 1);
                bfs_queue.add(last_used_node);
                last_used_node++;
                map_info[cn[1]][cn[2] + 1] = true;
            }

            //left expansion
            if (cn[2] > 0 && !map_info[cn[1]][cn[2] - 1] && game_map.map_v_walls[cn[1]][cn[2] - 1].isEnabled()) {
                prepare_snode(last_used_node, player, cn[3] + 1, cn[1], cn[2] - 1);
                bfs_queue.add(last_used_node);
                last_used_node++;
                map_info[cn[1]][cn[2] - 1] = true;
            }

            //up expansion
            if (cn[1] > 0 && !map_info[cn[1] - 1][cn[2]] && game_map.map_h_walls[cn[1] - 1][cn[2]].isEnabled()) {
                prepare_snode(last_used_node, player, cn[3] + 1, cn[1] - 1, cn[2]);
                bfs_queue.add(last_used_node);
                last_used_node++;
                map_info[cn[1] - 1][cn[2]] = true;
            }

            //down expansion
            if (cn[1] < game_panel.game_map.map_tiles.length - 1 && !map_info[cn[1] + 1][cn[2]] && game_map.map_h_walls[cn[1]][cn[2]].isEnabled()) {
                prepare_snode(last_used_node, player, cn[3] + 1, cn[1] + 1, cn[2]);
                bfs_queue.add(last_used_node);
                last_used_node++;
                map_info[cn[1] + 1][cn[2]] = true;
            }

        }

        return answer;
    }// VERIFIED WORKING CORRECTLY
    //make panel ready to lunch
    private void reset_panel(int num_players, JFrame parent) {

        initiate_instance();

        game_players = new Player[num_players];
        JLayeredPane game_playe_panel = this;

        game_screen = new JPanel();
        game_screen.setBounds(25, 25, 600, 600);

        game_screen.setLayout(new FlowLayout(FlowLayout.LEFT, 0, 0));
        make_ui(game_screen, game_map, 20, 20, parent.getWidth() * 8 / 10, parent.getHeight() * 8 / 10);
        update_ui(game_map, 20, 20, parent.getWidth() * 8 / 10, parent.getHeight() * 8 / 10,false);

        parent.addComponentListener(new ComponentAdapter() {
            @Override
            public void componentResized(ComponentEvent e) {
                game_playe_panel.setSize(parent.getWidth() * 8 / 10, parent.getHeight() * 8 / 10);
                game_screen.setSize(game_screen.getParent().getWidth(), game_screen.getParent().getHeight());
                update_ui(game_map, 20, 20, parent.getWidth() * 8 / 10, parent.getHeight() * 8 / 10, false);
                for (int i = 0; i < game_players.length; i++)
                    game_players[i].update_graphic();

            }
        });

        this.add(game_screen, 1, 0);
        for (int i = 0; i < num_players; i++)
            game_players[i] = new Player(i, this);


        for (int i = 0; i < game_players.length; i++)
            game_map.map_tiles[game_players[i].p_r][game_players[i].p_c].setValue(i);


    }// VERIFIED WORKING CORRECTLY
    //responsive ui for game
    private void make_ui(JPanel parent, Map game_map, int v_ratio, int h_ratio, int panel_width, int panel_height) {
        tile_width = (panel_width) / (-2 + game_map.map_tiles[0].length + game_map.map_v_walls[0].length * v_ratio / 100);
        v_wall_width = v_ratio * tile_width / 100;
        tile_height = panel_height / (game_map.map_tiles.length + game_map.map_h_walls.length * h_ratio / 100);
        h_wall_height = h_ratio * tile_height / 100;
        for (int r = game_map.map_h_walls.length + game_map.map_tiles.length - 1; r >= 0; r--) {
            for (int c = game_map.map_v_walls[0].length + game_map.map_tiles[0].length - 1; c >= 0; c--) {
                if (r % 2 == 0) {
                    if (c % 2 == 0) {
                        game_map.map_tiles[r / 2][c / 2] = new Tile(r / 2, c / 2, tile_width, tile_height, Tile_Color, Tile_back_Color, r / 2 + "," + c / 2);
                        parent.add(game_map.map_tiles[r / 2][c / 2], 1, 0);
                    } else {
                        game_map.map_v_walls[r / 2][c / 2] = new Wall(r / 2, c / 2, v_wall_width, tile_height, TYPE.VERTICAL, v_wall_Color, r / 2 + "," + c / 2);
                        parent.add(game_map.map_v_walls[r / 2][c / 2], 1, 0);
                    }
                } else {
                    if (c % 2 == 0) {
                        game_map.map_h_walls[r / 2][c / 2] = new Wall(r / 2, c / 2, tile_width, h_wall_height, TYPE.HORIZONTAL, h_wall_Color, r / 2 + "," + c / 2);
                        parent.add(game_map.map_h_walls[r / 2][c / 2], 1, 0);
                    } else {
                        game_map.map_squares[r / 2][c / 2] = new Square(r / 2, c / 2, v_wall_width, h_wall_height, square_Color, r / 2 + "," + c / 2);
                        parent.add(game_map.map_squares[r / 2][c / 2], 1, 0);
                    }

                }
            }
        }


    }
    //add new defined vars in here first
    private void update_ui(Map game_map, int v_ratio, int h_ratio, int width, int height,boolean reset) {
        tile_width = width / (1 + game_map.map_tiles[0].length + game_map.map_v_walls[0].length * v_ratio / 100);
        v_wall_width = v_ratio * tile_width / 100;
        tile_height = height / (1 + game_map.map_tiles.length + game_map.map_h_walls.length * h_ratio / 100);
        h_wall_height = h_ratio * tile_height / 100;
        for (int r = 0; r < game_map.map_h_walls.length + game_map.map_tiles.length; r++) {
            for (int c = 0; c < game_map.map_v_walls[0].length + game_map.map_tiles[0].length; c++) {
                if (r % 2 == 0) {
                    if (c % 2 == 0) {
                        game_map.map_tiles[r / 2][c / 2].setPreferredSize(new Dimension(tile_width, tile_height));
                        if(reset){ game_map.map_tiles[r / 2][c / 2].value = -1;}
                    } else {
                        game_map.map_v_walls[r / 2][c / 2].setPreferredSize(new Dimension(v_wall_width, tile_height));
                        if(reset){
                            game_map.map_v_walls[r / 2][c / 2].setEnabled(true);
                            game_map.map_v_walls[r / 2][c / 2].w_type = TYPE.VERTICAL;
                            game_map.map_v_walls[r / 2][c / 2].setBorder(new EmptyBorder(0, 0, 0, 0));
                            game_map.map_v_walls[r / 2][c / 2].setBackground(v_wall_Color);
                        }
                    }
                } else {
                    if (c % 2 == 0) {
                        game_map.map_h_walls[r / 2][c / 2].setPreferredSize(new Dimension(tile_width, h_wall_height));
                        if(reset){
                            game_map.map_h_walls[r / 2][c / 2].setEnabled(true);
                            game_map.map_h_walls[r / 2][c / 2].w_type = TYPE.HORIZONTAL;
                            game_map.map_h_walls[r / 2][c / 2].setBorder(new EmptyBorder(0, 0, 0, 0));
                            game_map.map_h_walls[r / 2][c / 2].setBackground(h_wall_Color);
                        }
                    } else {
                        game_map.map_squares[r / 2][c / 2].setPreferredSize(new Dimension(v_wall_width, h_wall_height));
                        if(reset){
                            game_map.map_squares[r / 2][c / 2].setEnabled(true);
                            game_map.map_squares[r / 2][c / 2].s_type = TYPE.NONE;
                            game_map.map_squares[r / 2][c / 2].setBorder(new EmptyBorder(0, 0, 0, 0));
                            game_map.map_squares[r / 2][c / 2].setBackground(square_Color);
                        }

                    }

                }
            }
        }
        this.updateUI();
    }
    //initiate class instance
    private void initiate_instance() {
        game_turn = 0;
        game_map = new Map(new Tile[9][9], new Square[8][8], new Wall[8][9], new Wall[9][8], game_players);
        node_pool = new Integer[81][5];
    }// VERIFIED WORKING CORRECTLY
    //agent turn play
    private void agent_game_play(int agent_num) throws InterruptedException {

        long startTime = System.nanoTime();

//        GameTree one_tree = new GameTree((byte) agent_num, (byte) 1);
//        one_tree.minimax(one_tree.tree_root);
        GameTree one_tree = new GameTree((byte) agent_num, (byte) 2);
//        one_tree.minimax(one_tree.tree_root);
//        one_tree = new GameTree((byte) agent_num, (byte) 3);
//        one_tree.minimax(one_tree.tree_root);
//        save_data();

        long endTime = System.nanoTime();

        System.out.println("Duration : " + (endTime - startTime) / 1000000 + "ms.");

        int action = one_tree.minimax(one_tree.tree_root);
        System.out.println("action = " + action);
        System.out.println("[" + one_tree.tree_root.node_actions[action].data[0] + "," + one_tree.tree_root.node_actions[action].data[1] + "," + one_tree.tree_root.node_actions[action].data[2] + "," + one_tree.tree_root.node_actions[action].data[3] + "]");
        //action structure in this game
        //[isMove][next_row][next_col]
        //0 is Move
        //1 is Block
        //node structure in this game
        //[NODE_TYPE][ACTION#1][ACTION#2][ACTION#3]...[ACTION#N]
        //action structure in this game
        //[isMove][next_row][next_col]
        //action numbers
        //0 for move
        //1 for place block
        //node_action[5] = [0,12,12]
        //our agent strategy for playing game
        if (one_tree.tree_root.node_actions[action].data[0] == 0) {
            game_map.map_tiles[one_tree.tree_root.node_actions[action].data[1]][one_tree.tree_root.node_actions[action].data[2]].tile_clicked();
            game_players[agent_num].walked_distance += 1;
        } else if (one_tree.tree_root.node_actions[action].data[0] == 1) {
            byte[] action_set = one_tree.tree_root.node_actions[action].data;
            if (action_set[3] == 0) {
                last_clicked_element = game_map.map_squares[action_set[1]][action_set[2]];
                game_map.map_squares[action_set[1]][action_set[2]].build_vertical_wall();
                game_players[agent_num].p_cor--;
            } else if (action_set[3] == 1) {
                last_clicked_element = game_map.map_squares[action_set[1]][action_set[2]];
                game_map.map_squares[action_set[1]][action_set[2]].build_horizontal_wall();
                game_players[agent_num].p_cor--;
            }

        }

        game_turn += 1;
        next_player(game_turn);

    }
    //routine for managing agents in game
    private void next_player(int game_turn) throws InterruptedException {
//        save_data();

        if (game_end()) {

            if (training_mode) {
                manage_genetic_process();
            }
            reset_game();
        }

        new Thread(() -> {
            try {
                if (game_turn % game_players.length != user_num) {
                    agent_game_play(game_turn % game_players.length);
                }
            } catch (InterruptedException e) {
                System.out.println("Interrupted during next_player()" + e.getMessage());
            }
        }).start();
        Thread.sleep(100);

    }
    //function for reset game
    private void reset_game() {
        for (int i = 0; i < 2; i++) {
            reset_game_player(i);
        }
        for (int i = 0; i < game_map.map_tiles.length; i++)
            for (int j = 0; j < game_map.map_tiles[0].length; j++)
                game_map.map_tiles[i][j].reset();

        for (int i = 0; i < game_map.map_squares.length; i++)
            for (int j = 0; j < game_map.map_squares[0].length; j++)
                game_map.map_squares[i][j].reset();

        for (int i = 0; i < game_map.map_v_walls.length; i++)
            for (int j = 0; j < game_map.map_v_walls[0].length; j++)
                game_map.map_v_walls[i][j].reset();

        for (int i = 0; i < game_map.map_h_walls.length; i++)
            for (int j = 0; j < game_map.map_h_walls[0].length; j++)
                game_map.map_h_walls[i][j].reset();

        game_map.h_square = 0L;
        game_map.v_square = 0L;
        game_turn = 0;
        winner = -1;

    }
    //function for checking game flow
    private boolean game_end() {
        winner = -1;
        if(game_players[0].p_c == 8 ) winner = 0;
        if(game_players[1].p_c == 0 ) winner = 1;
        return winner != -1;
    }
    //function for reset player
    private void reset_game_player(int i){
        int r_val = 0,c_val = 0;
        switch (i) {
            case 0:{r_val=4;c_val=0;break;}
            case 1:{r_val=4;c_val=8;break;}
            case 2:{r_val=0;c_val=4;break;}
            case 3:{r_val=8;c_val=4;break;}
        }
        game_map.map_tiles[game_players[i].p_r][game_players[i].p_c].value=-1;
        game_players[i].p_r=r_val;
        game_players[i].p_c = c_val;
        game_players[i].walked_distance = 0;
        game_players[i].p_cor = 20/game_players.length;
        game_map.map_tiles[game_players[i].p_r][game_players[i].p_c].value=i;
        game_players[i].p_image.setBounds(game_players[i].p_c * (tile_width + v_wall_width) + 15, game_players[i].p_r * (tile_height + h_wall_height) - 25, 75, 108);
        game_players[i].update_graphic();
    }
    //function for calculating player location
    private int cal_loc(int player){
        return game_players[player].p_r * game_map.map_tiles[0].length + game_players[player].p_c;
    }
    //function for returning new request
    private m_info req_gen(){
        return new m_info(game_map.v_square, game_map.h_square);
    }
    //move player inline
    private void move_player_inline(int orow, int ocol, int nrow, int ncol, int player) {
        game_map.map_tiles[orow][ocol].value = -1;
        game_players[player].p_r = nrow;
        game_players[player].p_c = ncol;
        game_map.map_tiles[nrow][ncol].value = player;

    }
    //add walls inline
    private void add_wall_inline(TYPE direction, int r, int c, boolean add) {
        int index = r * game_map.map_squares[0].length + c;
        if (add && direction.equals(TYPE.VERTICAL)) {
            game_map.map_squares[r][c].s_type = TYPE.VERTICAL;
            game_map.map_v_walls[r + 1][c].setEnabled(false);
            game_map.map_v_walls[r][c].setEnabled(false);
            game_map.v_square |= (1L << index);
        } else if (!add && direction.equals(TYPE.VERTICAL)) {
            game_map.map_squares[r][c].s_type = TYPE.NONE;
            game_map.map_v_walls[r + 1][c].setEnabled(true);
            game_map.map_v_walls[r][c].setEnabled(true);
            game_map.v_square &= ~(1L << index);
        } else if (add && direction.equals(TYPE.HORIZONTAL)) {
            game_map.map_squares[r][c].s_type = TYPE.HORIZONTAL;
            game_map.map_h_walls[r][c + 1].setEnabled(false);
            game_map.map_h_walls[r][c].setEnabled(false);
            game_map.h_square |= (1L << index);
        }
        else if (!add && direction.equals(TYPE.HORIZONTAL)) {
            game_map.map_squares[r][c].s_type = TYPE.NONE;
            game_map.map_h_walls[r][c + 1].setEnabled(true);
            game_map.map_h_walls[r][c].setEnabled(true);
            game_map.h_square &= ~(1L << index);
        }

    }
    //game object classes
    class Player {
        private int p_cor;
        private Color p_color;
        private Integer p_r, p_c;
        private JLabel[] p_cor_label;
        private int p_num;
        private JLabel p_image;
        private boolean select = false;
        private JLayeredPane parent;
        Integer walked_distance = 0;

        Player(int p_num, JLayeredPane parent) {
            this.p_cor = 20 / game_players.length;
            this.p_num = p_num;
            this.p_image = new JLabel();
            this.parent = parent;

            switch (p_num) {
                case 0: {
                    p_color = new Color(255, 0, 255);
                    p_r = 4;
                    p_c = 0;
                    p_image.setIcon(new ImageIcon(".\\player0"+"\\row-3-col-2-removebg-preview.png"));
                    break;
                }
                case 1: {
                    p_color = new Color(0, 255, 0);
                    p_r = 4;
                    p_c = 8;
                    p_image.setIcon(new ImageIcon(".\\player1"+"\\row-2-col-2-removebg-preview.png"));
                    break;
                }
                case 2: {
                    p_color = new Color(0, 0, 255);
                    p_r = 0;
                    p_c = 4;
                    p_image.setIcon(new ImageIcon(".\\player2"+"\\row-1-col-2-removebg-preview.png"));
                    break;
                }
                case 3: {
                    p_color = new Color(255, 255, 0);
                    p_r = 8;
                    p_c = 4;
                    p_image.setIcon(new ImageIcon(".\\player3"+"\\row-4-col-2-removebg-preview.png"));
                    break;
                }
            }
            game_map.map_tiles[p_r][p_c].value = p_num;
            p_image.setBounds(p_c * (tile_width + v_wall_width) + 15, p_r * (tile_height + h_wall_height) - 25, 75, 108);
            update_graphic();
            p_image.setCursor(new Cursor(Cursor.HAND_CURSOR));
            parent.add(p_image, 2, 0);
            game_map.map_tiles[p_r][p_c].setEnabled(false);

            p_image.addMouseListener(new MouseAdapter() {
                @Override
                public void mouseClicked(MouseEvent e) {
                    if (p_num == game_turn % 2 && p_num == user_num) {
                        if (last_clicked_element instanceof Square) {
                            ((Square) last_clicked_element).clear_square((Square) last_clicked_element, true, true);
                        }
                        if (!select) {
                            select = true;
                            inline_player_clicked(select, game_players[p_num].p_color, true, game_players[game_turn % game_players.length]);
                        } else {
                            select = false;
                            inline_player_clicked(select, Tile_Color, true, game_players[game_turn % game_players.length]);
                        }
                        last_clicked_element = p_image;
                    }
                }
            });

        }

        void inline_player_clicked(boolean enable, Color new_color, boolean recurse, Player player) {
            if (player.p_r - 1 >= 0) {
                if (game_map.map_h_walls[player.p_r - 1][player.p_c].isEnabled()) {
                    if (game_map.map_tiles[player.p_r - 1][player.p_c].value == -1) {
                        game_map.map_tiles[player.p_r - 1][player.p_c].setEnabled(enable);
                        game_map.map_tiles[player.p_r - 1][player.p_c].setBackground(new_color);
                    } else {
                        if (recurse)
                            inline_player_clicked(enable, new_color, false, game_players[game_map.map_tiles[player.p_r - 1][player.p_c].value]);
                    }
                }
            }
            if (player.p_r + 1 < game_map.map_tiles.length) {
                if (game_map.map_h_walls[player.p_r][player.p_c].isEnabled()) {
                    if (game_map.map_tiles[player.p_r + 1][player.p_c].value == -1) {
                        game_map.map_tiles[player.p_r + 1][player.p_c].setEnabled(enable);
                        game_map.map_tiles[player.p_r + 1][player.p_c].setBackground(new_color);
                    } else {
                        if (recurse)
                            inline_player_clicked(enable, new_color, false, game_players[game_map.map_tiles[player.p_r + 1][player.p_c].value]);
                    }
                }
            }
            if (player.p_c - 1 >= 0) {
                if (game_map.map_v_walls[player.p_r][player.p_c - 1].isEnabled()) {
                    if (game_map.map_tiles[player.p_r][player.p_c - 1].value == -1) {
                        game_map.map_tiles[player.p_r][player.p_c - 1].setEnabled(enable);
                        game_map.map_tiles[player.p_r][player.p_c - 1].setBackground(new_color);
                    } else {
                        if (recurse)
                            inline_player_clicked(enable, new_color, false, game_players[game_map.map_tiles[player.p_r][player.p_c - 1].value]);
                    }
                }
            }
            if (player.p_c + 1 < game_map.map_tiles[0].length) {
                if (game_map.map_v_walls[player.p_r][player.p_c].isEnabled()) {
                    if (game_map.map_tiles[player.p_r][player.p_c + 1].value == -1) {
                        game_map.map_tiles[player.p_r][player.p_c + 1].setEnabled(enable);
                        game_map.map_tiles[player.p_r][player.p_c + 1].setBackground(new_color);
                    } else {
                        if (recurse)
                            inline_player_clicked(enable, new_color, false, game_players[game_map.map_tiles[player.p_r][player.p_c + 1].value]);
                    }
                }

            }
        }

        void playMoveAnimation(DIR direction, int a_delay, int a_speed, int a_step) {
            ActionListener animation_move = null;
            int step = a_step;
            final int[] init = {0};
            int distance_h = (tile_width + v_wall_width) / step;
            int distance_v = (tile_height + h_wall_height) / step;
            int[] image_num = {-1};
            int[] distance = {-1, -1};
            Player current_player = this;
            switch (direction) {
                case UP: {
                    animation_move = e -> {
                        if (init[0] == step) {
                            return;
                        }
                        init[0] += 1;
                        current_player.p_image.setLocation(current_player.p_image.getX(), current_player.p_image.getY() - distance_v);
                        current_player.p_image.setIcon(new ImageIcon(".\\player" + current_player.p_num + "\\row-4-col-" + ((init[0]) % 3 + 1) + "-removebg-preview.png"));
                    };
                    break;
                }
                case LEFT: {
                    animation_move = e -> {
                        if (init[0] == step) {
                            return;
                        }
                        init[0] += 1;
                        current_player.p_image.setLocation(current_player.p_image.getX() - distance_h, current_player.p_image.getY());
                        current_player.p_image.setIcon(new ImageIcon(".\\player" + current_player.p_num + "\\row-2-col-" + ((init[0]) % 3 + 1) + "-removebg-preview.png"));
                    };
                    break;
                }
                case DOWN: {
                    animation_move = e -> {
                        if (init[0] == step) {
                            return;
                        }
                        init[0] += 1;
                        current_player.p_image.setLocation(current_player.p_image.getX(), current_player.p_image.getY() + distance_v);
                        current_player.p_image.setIcon(new ImageIcon(".\\player" + current_player.p_num + "\\row-1-col-" + ((init[0]) % 3 + 1) + "-removebg-preview.png"));
                    };
                    break;
                }
                case RIGHT: {
                    animation_move = e -> {
                        if (init[0] == step) {
                            return;
                        }
                        init[0] += 1;
                        current_player.p_image.setLocation(current_player.p_image.getX() + distance_h, current_player.p_image.getY());
                        current_player.p_image.setIcon(new ImageIcon(".\\player" + current_player.p_num + "\\row-3-col-" + ((init[0]) % 3 + 1) + "-removebg-preview.png"));
                    };
                    break;
                }
                case UU:
                case DD:
                case RR:
                case LL:
                case RU:
                case UR:
                case UL:
                case LU:
                case RD:
                case DR:
                case LD:
                case DL: {
                    switch (direction) {
                        case RU: {
                            image_num[0] = 4;
                            distance[0] = distance_h * step;
                            distance[1] = -distance_v * step;
                            break;
                        }
                        case UR: {
                            image_num[0] = 3;
                            distance[0] = distance_h * step;
                            distance[1] = -distance_v * step;
                            break;
                        }
                        case UL: {
                            image_num[0] = 2;
                            distance[0] = -distance_h * step;
                            distance[1] = -distance_v * step;
                            break;
                        }
                        case LU: {
                            image_num[0] = 4;
                            distance[0] = -distance_h * step;
                            distance[1] = -distance_v * step;
                            break;
                        }
                        case RD: {
                            image_num[0] = 1;
                            distance[0] = distance_h * step;
                            distance[1] = distance_v * step;
                            break;
                        }
                        case DR: {
                            image_num[0] = 3;
                            distance[0] = distance_h * step;
                            distance[1] = distance_v * step;
                            break;
                        }
                        case LD: {
                            image_num[0] = 1;
                            distance[0] = -distance_h * step;
                            distance[1] = distance_v * step;
                            break;
                        }
                        case DL: {
                            image_num[0] = 2;
                            distance[0] = -distance_h * step;
                            distance[1] = distance_v * step;
                            break;
                        }
                        case UU: {
                            image_num[0] = 4;
                            distance[0] = 0;
                            distance[1] = -2 * step * distance_v;
                            break;
                        }
                        case DD: {
                            image_num[0] = 1;
                            distance[0] = 0;
                            distance[1] = 2 * step * distance_v;
                            break;
                        }
                        case RR: {
                            image_num[0] = 3;
                            distance[0] = 2 * step * distance_h;
                            distance[1] = 0;
                            break;
                        }
                        case LL: {
                            image_num[0] = 2;
                            distance[0] = -2 * step * distance_h;
                            distance[1] = 0;
                            break;
                        }
                    }
                    animation_move = e -> {
                        if (init[0] == step) {
                            return;
                        }
                        init[0] += 1;
                        if (init[0] <= 6) {
                            current_player.p_image.setSize(current_player.p_image.getWidth() - 10, current_player.p_image.getHeight() - 15);
                            current_player.p_image.setIcon(new ImageIcon(".\\player" + current_player.p_num + "\\row-" + image_num[0] + "-col-2-removebg-preview-" + ((init[0]) / 2 % 3 + 1) + ".png"));
                        }
                        if (init[0] == 7) {
                            current_player.p_image.setLocation(current_player.p_image.getX() + distance[0], current_player.p_image.getY() + distance[1]);
                        } else if (init[0] >= 8 && init[0] < step - 1) {
                            current_player.p_image.setSize(current_player.p_image.getWidth() + 10, current_player.p_image.getHeight() + 15);
                            current_player.p_image.setIcon(new ImageIcon(".\\player" + current_player.p_num + "\\row-" + image_num[0] + "-col-2-removebg-preview-" + (3 - (init[0] + 1) / 2 % 3) + ".png"));
                        }
                        if (init[0] == step - 1) {
                            current_player.p_image.setIcon(new ImageIcon(".\\player" + current_player.p_num + "\\row-" + image_num[0] + "-col-2-removebg-preview.png"));
                        }

                    };
                    break;
                }
            }
            Timer animation = new Timer(a_speed, animation_move);
            animation.setInitialDelay(a_delay);
            animation.start();
            init[0] = 0;
        }

        void update_graphic() {
            p_image.setBounds(p_c * (tile_width + v_wall_width) + 15, p_r * (tile_height + h_wall_height) - 25, 75, 108);
        }
    }
    class Tile extends JButton {
        private int t_r, t_c;
        //if player exists on this board number of player (0,1,2,3) otherwise -1
        private int value;

        Tile(int t_r, int t_c, int width, int height, Color bg_color, Color fg_color, String text) {
            this.t_r = t_r;
            this.t_c = t_c;
            this.setPreferredSize(new Dimension(width, height));
            this.setVisible(true);
            this.value = -1;
            this.setBorder(new EmptyBorder(0, 0, 0, 0));
            this.setBackground(bg_color);
            this.setForeground(fg_color);
            this.setText(text);
            this.setEnabled(false);
            this.addActionListener(e -> {
                tile_clicked();
                game_turn++;
                try {
                    next_player(game_turn);
                } catch (InterruptedException e1) {
                    System.out.println("Interrupted at line 856");
                }
            });
        }

        void reset() {
            this.value = -1;
            this.setBorder(new EmptyBorder(0, 0, 0, 0));
            this.setBackground(Tile_Color);
            this.setForeground(Tile_back_Color);
            this.setEnabled(false);
        }

        void tile_clicked() {
            Player current_player = game_players[game_turn % game_players.length];
            deselect_tile(current_player);
            if (current_player.p_r - 1 >= 0 && game_map.map_tiles[current_player.p_r - 1][current_player.p_c].value != -1)
                deselect_tile(game_players[game_map.map_tiles[current_player.p_r - 1][current_player.p_c].value]);
            if (current_player.p_r + 1 < game_map.map_tiles.length && game_map.map_tiles[current_player.p_r + 1][current_player.p_c].value != -1)
                deselect_tile(game_players[game_map.map_tiles[current_player.p_r + 1][current_player.p_c].value]);
            if (current_player.p_c - 1 >= 0 && game_map.map_tiles[current_player.p_r][current_player.p_c - 1].value != -1)
                deselect_tile(game_players[game_map.map_tiles[current_player.p_r][current_player.p_c - 1].value]);
            if (current_player.p_c + 1 < game_map.map_tiles[0].length && game_map.map_tiles[current_player.p_r][current_player.p_c + 1].value != -1)
                deselect_tile(game_players[game_map.map_tiles[current_player.p_r][current_player.p_c + 1].value]);
            if (t_r - current_player.p_r == 1 && current_player.p_c - t_c == 1) {
                if (t_r - 1 >= 0 && game_map.map_tiles[t_r - 1][t_c].value != -1) {
                    reset_tile(current_player, DIR.LD);
                    current_player.playMoveAnimation(DIR.LD, 1500, 100, 15);
                } else if (t_c + 1 < game_map.map_tiles[0].length && game_map.map_tiles[t_r][t_c + 1].value != -1) {
                    reset_tile(current_player, DIR.DL);
                    current_player.playMoveAnimation(DIR.DL, 1500, 100, 15);
                }
            } else if (current_player.p_r - t_r == 1 && t_c - current_player.p_c == 1) {
                if (t_c - 1 >= 0 && game_map.map_tiles[t_r][t_c - 1].value != -1) {
                    reset_tile(current_player, DIR.UR);
                    current_player.playMoveAnimation(DIR.UR, 1500, 100, 15);
                } else if (t_r + 1 < game_map.map_tiles.length && game_map.map_tiles[t_r + 1][t_c].value != -1) {
                    reset_tile(current_player, DIR.RU);
                    current_player.playMoveAnimation(DIR.RU, 1500, 100, 15);
                }
            } else if (t_r - current_player.p_r == 1 && t_c - current_player.p_c == 1) {
                if (t_c - 1 >= 0 && game_map.map_tiles[t_r][t_c - 1].value != -1) {
                    reset_tile(current_player, DIR.DR);
                    current_player.playMoveAnimation(DIR.DR, 1500, 100, 15);
                } else if (t_r - 1 >= 0 && game_map.map_tiles[t_r - 1][t_c].value != -1) {
                    reset_tile(current_player, DIR.RD);
                    current_player.playMoveAnimation(DIR.RD, 1500, 100, 15);
                }
            } else if (current_player.p_r - t_r == 1 && current_player.p_c - t_c == 1) {
                if (t_c + 1 < game_map.map_tiles[0].length && game_map.map_tiles[t_r][t_c + 1].value != -1) {
                    reset_tile(current_player, DIR.UL);
                    current_player.playMoveAnimation(DIR.UL, 1500, 100, 15);
                } else if (t_r + 1 < game_map.map_tiles.length && game_map.map_tiles[t_r + 1][t_c].value != -1) {
                    reset_tile(current_player, DIR.LU);
                    current_player.playMoveAnimation(DIR.LU, 1500, 100, 15);
                }
            } else if (t_r - current_player.p_r == 1) {
                reset_tile(current_player, DIR.DOWN);
                current_player.playMoveAnimation(DIR.DOWN, 1050, 150, 7);
            } else if (current_player.p_r - t_r == 1) {
                reset_tile(current_player, DIR.UP);
                current_player.playMoveAnimation(DIR.UP, 1050, 150, 7);
            } else if (current_player.p_c - t_c == 1) {
                reset_tile(current_player, DIR.LEFT);
                current_player.playMoveAnimation(DIR.LEFT, 1050, 150, 7);
            } else if (t_c - current_player.p_c == 1) {
                reset_tile(current_player, DIR.RIGHT);
                current_player.playMoveAnimation(DIR.RIGHT, 1050, 150, 7);
            } else if (t_c - current_player.p_c == 2) {
                reset_tile(current_player, DIR.RR);
                current_player.playMoveAnimation(DIR.RR, 1500, 100, 15);
            } else if (current_player.p_c - t_c == 2) {
                reset_tile(current_player, DIR.LL);
                current_player.playMoveAnimation(DIR.LL, 1500, 100, 15);
            } else if (t_r - current_player.p_r == 2) {
                reset_tile(current_player, DIR.DD);
                current_player.playMoveAnimation(DIR.DD, 1500, 100, 15);
            } else if (current_player.p_r - t_r == 2) {
                reset_tile(current_player, DIR.UU);
                current_player.playMoveAnimation(DIR.UU, 1500, 100, 15);
            }
        }

        void deselect_tile(Player player) {
            game_map.map_tiles[player.p_r][player.p_c].setBackground(Tile_Color);
            if (player.p_r - 1 >= 0) {
                game_map.map_tiles[player.p_r - 1][player.p_c].setBackground(Tile_Color);
                game_map.map_tiles[player.p_r - 1][player.p_c].setEnabled(false);
            }
            if (player.p_r + 1 < game_map.map_tiles.length) {
                game_map.map_tiles[player.p_r + 1][player.p_c].setBackground(Tile_Color);
                game_map.map_tiles[player.p_r + 1][player.p_c].setEnabled(false);
            }
            if (player.p_c - 1 >= 0) {
                game_map.map_tiles[player.p_r][player.p_c - 1].setBackground(Tile_Color);
                game_map.map_tiles[player.p_r][player.p_c - 1].setEnabled(false);
            }
            if (player.p_c + 1 < game_map.map_tiles[0].length) {
                game_map.map_tiles[player.p_r][player.p_c + 1].setBackground(Tile_Color);
                game_map.map_tiles[player.p_r][player.p_c + 1].setEnabled(false);
            }
            player.select = false;
        }

        void reset_tile(Player player, DIR direction) {
            game_map.map_tiles[player.p_r][player.p_c].value = -1;
            deselect_tile(player);
            switch (direction) {
                case RIGHT: {
                    player.p_c++;
                    break;
                }
                case LEFT: {
                    player.p_c--;
                    break;
                }
                case UP: {
                    player.p_r--;
                    break;
                }
                case DOWN: {
                    player.p_r++;
                    break;
                }
                case DL: {
                    player.p_c -= 1;
                    player.p_r += 1;
                    break;
                }
                case DR: {
                    player.p_c += 1;
                    player.p_r += 1;
                    break;
                }
                case UL: {
                    player.p_c -= 1;
                    player.p_r -= 1;
                    break;
                }
                case UR: {
                    player.p_c += 1;
                    player.p_r -= 1;
                    break;
                }
                case LD: {
                    player.p_c -= 1;
                    player.p_r += 1;
                    break;
                }
                case LU: {
                    player.p_c -= 1;
                    player.p_r -= 1;
                    break;
                }
                case RU: {
                    player.p_c += 1;
                    player.p_r -= 1;
                    break;
                }
                case RD: {
                    player.p_c += 1;
                    player.p_r += 1;
                    break;
                }
                case RR: {
                    player.p_c += 2;
                    break;
                }
                case LL: {
                    player.p_c -= 2;
                    break;
                }
                case DD: {
                    player.p_r += 2;
                    break;
                }
                case UU: {
                    player.p_r -= 2;
                    break;
                }
                case NONE: {
                    break;
                }
            }
            game_map.map_tiles[player.p_r][player.p_c].value = player.p_num;
        }

        void setValue(int value) {
            this.value = value;
        }
    }
    class Square extends JButton {
        int r, c;
        TYPE s_type;
        private boolean isVerticalSelected = false;

        Square(int r, int c, int width, int height, Color bg_color, String tool_tip_text) {

            this.r = r;
            this.c = c;
            this.setPreferredSize(new Dimension(width, height));
            this.s_type = TYPE.NONE;
            this.setVisible(true);
            this.setBorder(new EmptyBorder(0, 0, 0, 0));
            this.setBackground(bg_color);
            this.setToolTipText(tool_tip_text);

            Square parent = this;

            this.addActionListener(e -> {
                if (game_players[game_turn%game_players.length].p_num == user_num) {
                    if (last_clicked_element == null) last_clicked_element = this;

                    if (isVerticalSelected) {
                        clear_square(parent, false, true);
                        if (game_map.map_v_walls[parent.r][parent.c].isEnabled() && game_map.map_v_walls[parent.r + 1][parent.c].isEnabled()) {
                            update_square(isVerticalSelected, last_clicked_element);
                        }
                        isVerticalSelected = false;
                    } else {
                        clear_square(parent, true, false);
                        if (game_map.map_h_walls[parent.r][parent.c].isEnabled() && game_map.map_h_walls[parent.r][parent.c + 1].isEnabled()) {
                            update_square(isVerticalSelected, last_clicked_element);
                        }
                        isVerticalSelected = true;
                    }
                }
            });
            this.addKeyListener(new KeyAdapter() {
                @Override
                public void keyPressed(KeyEvent e) {
                    if (game_players[game_turn % game_players.length].p_num == user_num) {
                        if (e.getKeyCode() == KeyEvent.VK_ENTER) {
                            if (isVerticalSelected) {
                                //it is horizontal
                                game_map.map_h_walls[parent.r][parent.c].setEnabled(false);
                                game_map.map_h_walls[parent.r][parent.c + 1].setEnabled(false);
                                if (check_block_group()) {
                                    build_horizontal_wall();
                                    game_turn += 1;
                                    try {
                                        next_player(game_turn);
                                    } catch (InterruptedException e1) {
                                        System.out.println("Interrupted at line 1091");
                                    }
                                } else {
                                    //print error box

                                    game_map.map_h_walls[parent.r][parent.c].setEnabled(true);
                                    game_map.map_h_walls[parent.r][parent.c + 1].setEnabled(true);
                                }

                            } else {
                                //it is vertical
                                game_map.map_v_walls[parent.r][parent.c].setEnabled(false);
                                game_map.map_v_walls[parent.r + 1][parent.c].setEnabled(false);
                                if (check_block_group()) {
                                    build_vertical_wall();
                                    game_turn += 1;
                                    try {
                                        next_player(game_turn);
                                    } catch (InterruptedException e1) {
                                        System.out.println("Interrupted at line 1091");
                                    }

                                } else {
                                    //print error box
                                    game_map.map_v_walls[parent.r][parent.c].setEnabled(true);
                                    game_map.map_v_walls[parent.r + 1][parent.c].setEnabled(true);
                                }

                            }
                        }
                    }
                }
            });
        }

        void reset(){
            this.s_type = TYPE.NONE;
            this.setVisible(true);
            this.setBorder(new EmptyBorder(0, 0, 0, 0));
            this.setBackground(square_Color);
        }

        void build_horizontal_wall() {
            if (last_clicked_element.equals(this)) {
                game_map.map_h_walls[this.r][this.c].setEnabled(false);
                game_map.map_h_walls[this.r][this.c].setBorder(new MatteBorder(1, 1, 1, 0, Color.white));
                game_map.map_h_walls[this.r][this.c + 1].setEnabled(false);
                game_map.map_h_walls[this.r][this.c + 1].setBorder(new MatteBorder(1, 0, 1, 1, Color.white));
                game_map.map_h_walls[this.r][this.c].setBackground(game_players[game_turn % game_players.length].p_color);
                game_map.map_h_walls[this.r][this.c + 1].setBackground(game_players[game_turn % game_players.length].p_color);
                this.setBackground(game_players[game_turn % game_players.length].p_color);
                this.setEnabled(false);
                this.setBorder(new MatteBorder(1, 0, 1, 0, Color.white));
                this.s_type = TYPE.HORIZONTAL;
                last_clicked_element = null;
                game_map.h_square |= (1L << (this.r * game_map.map_squares[0].length + this.c));
            }
        }

        void build_vertical_wall() {
            if (last_clicked_element.equals(this)) {
                game_map.map_v_walls[this.r][this.c].setEnabled(false);
                game_map.map_v_walls[this.r][this.c].setBorder(new MatteBorder(1, 1, 0, 1, Color.white));
                game_map.map_v_walls[this.r + 1][this.c].setEnabled(false);
                game_map.map_v_walls[this.r + 1][this.c].setBorder(new MatteBorder(0, 1, 1, 1, Color.white));
                game_map.map_v_walls[this.r][this.c].setBackground(game_players[game_turn % game_players.length].p_color);
                game_map.map_v_walls[this.r + 1][this.c].setBackground(game_players[game_turn % game_players.length].p_color);
                this.setBackground(game_players[game_turn % game_players.length].p_color);
                this.setEnabled(false);
                this.setBorder(new MatteBorder(0, 1, 0, 1, Color.white));
                this.s_type = TYPE.VERTICAL;
                last_clicked_element = null;
                game_map.v_square |= (1L << (this.r * game_map.map_squares[0].length + this.c));
            }
        }

        void update_square(boolean isVerticalSelected, Component last) {
            Player current_player = game_players[game_turn % game_players.length];
            this.setBackground(current_player.p_color);
            if (isVerticalSelected && last instanceof Square) {
                if (!last.equals(this)) clear_square((Square) last, true, true);
                game_map.map_v_walls[this.r][this.c].setBackground(current_player.p_color);
                game_map.map_v_walls[this.r + 1][this.c].setBackground(current_player.p_color);
            } else if (isVerticalSelected && last instanceof JLabel) {
                game_map.map_tiles[current_player.p_r][current_player.p_c].reset_tile(current_player, DIR.NONE);
                game_map.map_v_walls[this.r][this.c].setBackground(current_player.p_color);
                game_map.map_v_walls[this.r + 1][this.c].setBackground(current_player.p_color);
            } else if (!isVerticalSelected && last instanceof Square) {
                if (!last.equals(this)) clear_square((Square) last, true, true);
                game_map.map_h_walls[this.r][this.c].setBackground(current_player.p_color);
                game_map.map_h_walls[this.r][this.c + 1].setBackground(current_player.p_color);
            } else if (!isVerticalSelected && last instanceof JLabel) {
                game_map.map_tiles[current_player.p_r][current_player.p_c].reset_tile(current_player, DIR.NONE);
                game_map.map_h_walls[this.r][this.c].setBackground(current_player.p_color);
                game_map.map_h_walls[this.r][this.c + 1].setBackground(current_player.p_color);
            }
            last_clicked_element = this;
        }

        void clear_square(Square parent, boolean vertical, boolean horizontal) {
            parent.setBackground(square_Color);
            if (horizontal && game_map.map_h_walls[parent.r][parent.c].isEnabled())
                if(!(game_map.map_h_walls[parent.r][parent.c].getBorder() instanceof MatteBorder))game_map.map_h_walls[parent.r][parent.c].setBackground(h_wall_Color);
            if (horizontal && game_map.map_h_walls[parent.r][parent.c + 1].isEnabled())
                if(!(game_map.map_h_walls[parent.r][parent.c+1].getBorder() instanceof MatteBorder))game_map.map_h_walls[parent.r][parent.c + 1].setBackground(h_wall_Color);
            if (vertical && game_map.map_v_walls[parent.r][parent.c].isEnabled())
                if(!(game_map.map_v_walls[parent.r][parent.c].getBorder() instanceof MatteBorder))game_map.map_v_walls[parent.r][parent.c].setBackground(v_wall_Color);
            if (vertical && game_map.map_v_walls[parent.r + 1][parent.c].isEnabled())
                if(!(game_map.map_v_walls[parent.r+1][parent.c].getBorder() instanceof MatteBorder))game_map.map_v_walls[parent.r + 1][parent.c].setBackground(v_wall_Color);
        }

    }
    class Wall extends JButton {

        int r, c;
        TYPE w_type;

        Wall(int r, int c, int width, int height, TYPE w_type, Color bg_color, String tool_tip_text) {
            this.r = r;
            this.c = c;
            this.setPreferredSize(new Dimension(width, height));
            this.w_type = w_type;
            this.setVisible(true);
            this.setBorder(new EmptyBorder(0, 0, 0, 0));
            this.setBackground(bg_color);
            this.setToolTipText(tool_tip_text);
        }

        void reset() {
            this.setVisible(true);
            this.setBorder(new EmptyBorder(0, 0, 0, 0));
            switch (this.w_type) {
                case VERTICAL:{this.setBackground(v_wall_Color);break;}
                case HORIZONTAL:{this.setBackground(h_wall_Color);break;}
            }
        }
    }
    class Map {
        Tile[][] map_tiles;
        Square[][] map_squares;
        Wall[][] map_h_walls, map_v_walls;
        Player[] map_players;
        long v_square,h_square;

        Map(Tile[][] map_tiles, Square[][] map_squares, Wall[][] map_h_walls, Wall[][] map_v_walls, Player[] map_players) {
            this.map_tiles = map_tiles;
            this.map_squares = map_squares;
            this.map_h_walls = map_h_walls;
            this.map_v_walls = map_v_walls;
            this.map_players = map_players;
            v_square = h_square = 0L;
        }

    }
    //first change the map after that return map to previous state so we do not need any memory for maps
    //we must change location of players as well but at last they must be undone
    class GameTree {
        byte agent_num;
        byte tree_depth;
        Node tree_root;
        short branch_factor = 0;
        int tree_nodes = 0;
        GameTree(byte agent_num, byte tree_depth) {
            this.agent_num = agent_num;
            this.tree_depth = tree_depth;
            tree_root = new Node();
            tree_root.depth = 0;
            prepare_node(tree_root);
            build_tree(tree_root);
        }
        //node structure in this game
        //[NODE_TYPE][ACTION#1][ACTION#2][ACTION#3]...[ACTION#N]
        //action structure in this game
        //[isMove][next_row][next_col]
        //action numbers
        //0 for move
        //1 for place block
        //node_action[5] = [0,12,12]
        //our agent strategy for playing game
        void prepare_node(Node current_node) {
            tree_nodes++;
//            System.out.println("working on <" + (tree_nodes - 1) + ">");

            //check node and decide if its value or min or max
            if (current_node.depth == tree_depth
                    || game_players[0].p_c == game_map.map_tiles[0].length - 1
                    || game_players[1].p_c == 0
                    || game_players.length == 4 && game_players[2].p_r == game_map.map_tiles.length - 1
                    || game_players.length == 4 && game_players[3].p_r == 0) {
                //if we are in correct depth by using heuristic function we
                //determine the value of node and then close the function
                current_node.node_type = 0;
                return;
            } else if (current_node.depth % game_players.length == 0) {
                current_node.node_type = 1;
                current_node.value = -1000000.0;
            } else {
                current_node.node_type = -1;
                current_node.value = 1000000.0;
            }

            //first allocate memory for actions
            branch_factor = 0;
            byte[][] max_action = new byte[136][4];
            //agent moving up,down,left,right
            Player current_player = game_players[cur_ply(current_node)];
            check_current_location(current_player.p_r, current_player.p_c, max_action, true);

            //check placing block actions
            if (current_player.p_cor >= 1) {
                for (int i = 0; i < game_panel.game_map.map_squares.length; i++) {
                    for (int j = 0; j < game_panel.game_map.map_squares[0].length; j++) {
                        if (game_map.map_squares[i][j].s_type == TYPE.NONE) {
                            if (check_square(0, i, j)) {

                                add_wall_inline(TYPE.VERTICAL, i, j, true);

                                if (check_block_group()) {
                                    add_block(i, j, (byte) 0, max_action);
                                }

                                add_wall_inline(TYPE.VERTICAL, i, j, false);

                            }
                            if (check_square(1, i, j)) {

                                add_wall_inline(TYPE.HORIZONTAL, i, j, true);

                                if (check_block_group()) {
                                    add_block(i, j, (byte) 1, max_action);
                                }

                                add_wall_inline(TYPE.HORIZONTAL, i, j, false);

                            }
                        }
                    }
                }
            }


            //push all actions
            current_node.node_actions = new Transition[branch_factor];
            for (int i = 0; i < branch_factor; i++) {
                current_node.node_actions[i] = new Transition(max_action[i], new Node());
                current_node.node_actions[i].result.depth = (byte) (current_node.depth + 1);
            }


        }
        //function for finding legal square for current player to build wall
        private boolean check_square(int mode, int c_i, int c_j) {
            if (mode == 1)
                return ((c_j == 0) || (c_j > 0 && game_map.map_squares[c_i][c_j - 1].s_type != TYPE.HORIZONTAL)) && ((c_j == game_panel.game_map.map_squares[0].length - 1) || (c_j < game_panel.game_map.map_squares[0].length - 1 && game_map.map_squares[c_i][c_j + 1].s_type != TYPE.HORIZONTAL));
            if (mode == 0)
                return ((c_i == 0) || (c_i > 0 && game_map.map_squares[c_i - 1][c_j].s_type != TYPE.VERTICAL)) && ((c_i == game_panel.game_map.map_squares.length - 1) || (c_i < game_panel.game_map.map_squares.length - 1 && game_map.map_squares[c_i + 1][c_j].s_type != TYPE.VERTICAL));
            return false;
        }
        //find current player
        int cur_ply(Node parent){
            return (agent_num + parent.depth) % game_players.length;
        }
        //current turn must be zero
        void build_tree(Node parent) {

            byte[] cer = memoize[cal_loc(0)][cal_loc(1)][agent_num].get(req_gen());
            if (cer != null && cer[2] == -1) {
                parent.cut = true;
                System.err.println("tree->illegal");
                return;
            }


            if (parent.node_type == 0) {

                if (memoize[cal_loc(0)][cal_loc(1)][agent_num].containsKey(req_gen())) {
                    parent.value = heu_calc(memoize[cal_loc(0)][cal_loc(1)][agent_num].get(req_gen()));
                    parent.calculated = true;
//                    System.out.println("leaf->cut");
                }
                else {
                    parent.value = heuristic(parent);
                }

            }
            else {

                if (tree_depth - parent.depth <= MAX_TREE_HEU_DEPTH && tree_memo[cal_loc(0)][cal_loc(1)][cur_ply(parent)][(parent.node_type == -1 ? 0 : 1)][tree_depth - parent.depth - 1].containsKey(req_gen())) {

                    parent.value = tree_memo[cal_loc(0)][cal_loc(1)][cur_ply(parent)][(parent.node_type == -1 ? 0 : 1)][tree_depth - parent.depth - 1].get(req_gen());
                    parent.calculated = true;
                    System.err.println("tree->cut");
                    return;
                }

                for (Transition action : parent.node_actions) {

                    int current_player = cur_ply(parent);
                    //change,calculate,restore
                    if (action.data[0] == 0) {
                        byte i_r = (byte) (game_players[current_player].p_r + 0);
                        byte i_c = (byte) (game_players[current_player].p_c + 0);
                        move_player_inline(i_r,i_c,action.data[1],action.data[2],current_player);
//                        game_map.map_tiles[i_r][i_c].value = -1;
//                        game_players[current_player].p_r = (int) action.data[1];
//                        game_players[current_player].p_c = (int) action.data[2];
//                        game_map.map_tiles[action.data[1]][action.data[2]].value = current_player;

                        if (action.result.node_type!=0 && tree_depth - action.result.depth <= MAX_TREE_HEU_DEPTH && tree_memo[cal_loc(0)][cal_loc(1)][cur_ply(action.result)][(action.result.node_type == -1 ? 0 : 1)][tree_depth - action.result.depth - 1].containsKey(req_gen())) {
                            action.result.value = tree_memo[cal_loc(0)][cal_loc(1)][cur_ply(action.result)][(action.result.node_type == -1 ? 0 : 1)][tree_depth - action.result.depth - 1].get(req_gen());
                            action.result.calculated = true;
                            System.err.println("tree->cut");
                        }
                        else {
                            prepare_node(action.result);
                            build_tree(action.result);
                        }

                        move_player_inline(game_players[current_player].p_r,game_players[current_player].p_c,i_r,i_c,current_player);
//                        game_map.map_tiles[game_players[current_player].p_r][game_players[current_player].p_c].value = -1;
//                        game_players[current_player].p_r = (int) i_r;
//                        game_players[current_player].p_c = (int) i_c;
//                        game_map.map_tiles[i_r][i_c].value = current_player;

                    } else if (action.data[0] == 1) {
                        if (action.data[3] == 0) {

                            add_wall_inline(TYPE.VERTICAL, action.data[1], action.data[2], true);
                            game_players[agent_num].p_cor -= 1;

                            if (action.result.node_type != 0 && tree_depth - action.result.depth <= MAX_TREE_HEU_DEPTH && tree_memo[cal_loc(0)][cal_loc(1)][cur_ply(action.result)][(action.result.node_type == -1 ? 0 : 1)][tree_depth - action.result.depth - 1].containsKey(req_gen())) {

                                action.result.value = tree_memo[cal_loc(0)][cal_loc(1)][cur_ply(action.result)][(action.result.node_type == -1 ? 0 : 1)][tree_depth - action.result.depth - 1].get(req_gen());
                                action.result.calculated = true;
                                System.err.println("tree->cut");
                            } else {
                                prepare_node(action.result);
                                build_tree(action.result);
                            }


                            add_wall_inline(TYPE.VERTICAL, action.data[1], action.data[2], false);
                            game_players[agent_num].p_cor += 1;

                        } else if (action.data[3] == 1) {

                            add_wall_inline(TYPE.HORIZONTAL, action.data[1], action.data[2], true);
                            game_players[agent_num].p_cor -= 1;

                            if (action.result.node_type != 0 && tree_depth - action.result.depth <= MAX_TREE_HEU_DEPTH && tree_memo[cal_loc(0)][cal_loc(1)][cur_ply(action.result)][(action.result.node_type == -1 ? 0 : 1)][tree_depth - action.result.depth - 1].containsKey(req_gen())) {

                                action.result.value = tree_memo[cal_loc(0)][cal_loc(1)][cur_ply(action.result)][(action.result.node_type == -1 ? 0 : 1)][tree_depth - action.result.depth - 1].get(req_gen());
                                action.result.calculated = true;
                                System.err.println("tree->cut");
                            } else {
                                prepare_node(action.result);
                                build_tree(action.result);
                            }


                            add_wall_inline(TYPE.HORIZONTAL, action.data[1], action.data[2], false);
                            game_players[agent_num].p_cor += 1;

                        }
                    }
                }

            }

        }//checked
        boolean legal_move(int row, int col, DIR direction, Map start_map) {
            switch (direction) {
                case UP:
                    return row > 0 && start_map.map_h_walls[row - 1][col].isEnabled();
                case DOWN:
                    return row < start_map.map_tiles.length - 1 && start_map.map_h_walls[row][col].isEnabled();
                case LEFT:
                    return col > 0 && start_map.map_v_walls[row][col - 1].isEnabled();
                case RIGHT:
                    return col < start_map.map_tiles[0].length - 1 && start_map.map_v_walls[row][col].isEnabled();
            }
            return false;
        }
        void add_move(int row, int col, DIR direction, byte[][] action_array) {
            switch (direction) {
                case RIGHT: {
                    action_array[branch_factor][0] = 0;
                    action_array[branch_factor][1] = (byte) (row);
                    action_array[branch_factor][2] = (byte) (col + 1);
                    branch_factor += 1;
                    return;
                }
                case UP: {
                    action_array[branch_factor][0] = 0;
                    action_array[branch_factor][1] = (byte) (row - 1);
                    action_array[branch_factor][2] = (byte) (col);
                    branch_factor += 1;
                    return;
                }
                case DOWN: {
                    action_array[branch_factor][0] = 0;
                    action_array[branch_factor][1] = (byte) (row + 1);
                    action_array[branch_factor][2] = (byte) (col);
                    branch_factor += 1;
                    return;
                }
                case LEFT: {
                    action_array[branch_factor][0] = 0;
                    action_array[branch_factor][1] = (byte) (row);
                    action_array[branch_factor][2] = (byte) (col - 1);
                    branch_factor += 1;
                    return;
                }
            }
        }
        void add_block(int row, int col, byte direction, byte[][] action_array) {
            //1 for horizontal
            //0 for vertical
            action_array[branch_factor][0] = 1;
            action_array[branch_factor][1] = (byte) row;
            action_array[branch_factor][2] = (byte) col;
            action_array[branch_factor][3] = direction;
//            System.out.println("block["+row+","+col+"]->"+direction+":"+branch_factor);
            branch_factor += 1;
        }
        void check_current_location(int row, int col, byte[][] action_array, boolean recurse) {
            if (legal_move(row, col, DIR.UP, game_map)) {
                if (game_map.map_tiles[row - 1][col].value == -1)
                    add_move(row, col, DIR.UP, action_array);
                else if (recurse)
                    check_current_location(row - 1, col, action_array, false);
            }
            if (legal_move(row, col, DIR.DOWN, game_map)) {
                if (game_map.map_tiles[row + 1][col].value == -1)
                    add_move(row, col, DIR.DOWN, action_array);
                else if (recurse)
                    check_current_location(row + 1, col, action_array, false);
            }
            if (legal_move(row, col, DIR.LEFT, game_map)) {
                if (game_map.map_tiles[row][col - 1].value == -1)
                    add_move(row, col, DIR.LEFT, action_array);
                else if (recurse)
                    check_current_location(row, col - 1, action_array, false);
            }
            if (legal_move(row, col, DIR.RIGHT, game_map)) {
                if (game_map.map_tiles[row][col + 1].value == -1)
                    add_move(row, col, DIR.RIGHT, action_array);
                else if (recurse)
                    check_current_location(row, col + 1, action_array, false);
            }
        }
        double heu_calc(byte[] p_md) {
            switch (agent_num) {
                case 0 :return  current_generation[0][1] * p_md[1] - current_generation[0][0] * p_md[0];
                case 1 :return  current_generation[1][0] * p_md[0] - current_generation[1][1] * p_md[1];
            }
            return -1;
        }
        double heuristic(Node parent) {

            byte[] p_md = {0,0,0};

            for (int i = 0; i < game_players.length; i++) {
                p_md[i] = (byte) check_block_player(i);
                if (p_md[i] == -1) {
                    p_md[2] = -1;
                    break;
                }
            }


            double final_heu = heu_calc(p_md);

            memoize[cal_loc(0)][cal_loc(1)][agent_num].put(new m_info(game_map.v_square, game_map.h_square), p_md);
//            System.out.println("memo save in : 1689");

            return final_heu;
        }
        void change_map(boolean change, int type, int row, int col, int direction, Node target) {
            if (type == 0) {
                game_players[cur_ply(target)].p_r = row;
                game_players[cur_ply(target)].p_c = col;
                return;
            }
            int index = row * game_map.map_squares[0].length + col;
            if (change) {
                if (direction == 0) {
                    game_map.v_square |= (1L << index);
                } else {
                    game_map.h_square |= (1L << index);
                }
            } else {
                if (direction == 0) {
                    game_map.v_square &= ~(1L << index);
                } else {
                    game_map.h_square &= ~(1L << index);
                }
            }
        }
        Integer minimax(Node target) {
            calculated += 1;
            if (calculated % 1000000L == 0) {
                System.out.println(calculated / 1000000L + "M.");
            }
            target.alpha = -1000000.0;
            target.beta = 1000000.0;
            target.value = -1000000.0;
//            System.out.println("TREE SIZE " + tree_nodes);
//            System.out.println("PROCESS : " + process_meter);
            return (int) find_max(target);
        }
        double find_max(Node target) {
            short index = 0;

            for (int i = 0; i < target.node_actions.length; i++) {


                if (target.cut) {
                    continue;
                }

                byte[] data = target.node_actions[i].data;
                int p_r = game_players[cur_ply(target)].p_r;
                int p_c = game_players[cur_ply(target)].p_c;
                change_map(true, data[0], data[1], data[2], data[3], target);


                if (target.node_actions[i].result.node_type != 0) {
                    target.node_actions[i].result.alpha = target.alpha;
                    target.node_actions[i].result.beta = target.beta;
                }


                switch (target.node_actions[i].result.node_type) {
                    case 0: {
                        if (target.value < target.node_actions[i].result.value) {
//                            System.out.print("[" + target.value + "->" + target.node_actions[i].result.value + "," + i + "]");
                            target.value = target.node_actions[i].result.value;
                            target.alpha = target.value;
                            index = (short) i;
                        }
                        break;
                    }
                    case 1: {
                        double max_res;
                        if (target.node_actions[i].result.calculated) {
                            max_res = target.node_actions[i].result.value;
                            System.err.println("tree::::cut");
                        } else {
                            max_res = find_max(target.node_actions[i].result);
                            if (tree_depth - target.node_actions[i].result.depth <= MAX_TREE_HEU_DEPTH && !tree_memo[cal_loc(0)][cal_loc(1)][cur_ply(target.node_actions[i].result)][1][tree_depth - target.node_actions[i].result.depth - 1].containsKey(req_gen())) {
                                tree_memo[cal_loc(0)][cal_loc(1)][cur_ply(target.node_actions[i].result)][1][tree_depth - target.node_actions[i].result.depth - 1].put(req_gen(), max_res);
                            }
                        }
                        if (target.value < max_res) {
                            target.value = max_res;
                            target.alpha = target.value;
                            index = (short) i;
                        }
                        break;
                    }
                    case -1: {
                        double min_res;
                        if (target.node_actions[i].result.calculated) {
                            min_res = target.node_actions[i].result.value;
                            System.err.println("tree::::cut");
                        } else {
                            min_res = find_min(target.node_actions[i].result);
                            if (tree_depth - target.node_actions[i].result.depth <= MAX_TREE_HEU_DEPTH && !tree_memo[cal_loc(0)][cal_loc(1)][cur_ply(target.node_actions[i].result)][0][tree_depth - target.node_actions[i].result.depth - 1].containsKey(req_gen())) {
                                tree_memo[cal_loc(0)][cal_loc(1)][cur_ply(target.node_actions[i].result)][0][tree_depth - target.node_actions[i].result.depth - 1].put(req_gen(), min_res);
                            }
                        }
                        if (target.value < min_res) {
                            target.value = (byte) min_res;
                            target.alpha = target.value;
                            index = (short) i;
                        }
                        break;
                    }
                }

                //TODO active this later
//TODO                if (target.alpha >= target.beta) {
//TODO                    System.out.print("pruned!");
//TODO                    break;
//TODO                }

                if (data[0] == 0) {
                    change_map(false, data[0], p_r, p_c, data[3], target);
                } else {
                    change_map(false, data[0], data[1], data[2], data[3], target);
                }

            }

            if (target.depth == 0) {
                return index;
            }

            return target.value;

        }
        double find_min(Node target) {
            short index = 0;

            for (int i = 0; i < target.node_actions.length; i++) {

                if (target.cut) {
                    continue;
                }

                byte[] data = target.node_actions[i].data;
                int p_r = game_players[cur_ply(target)].p_r;
                int p_c = game_players[cur_ply(target)].p_c;
                change_map(true, data[0], data[1], data[2], data[3], target);

                if (target.node_actions[i].result.node_type != 0) {
                    target.node_actions[i].result.alpha = target.alpha;
                    target.node_actions[i].result.beta = target.beta;
                }

                switch (target.node_actions[i].result.node_type) {
                    case 0: {
                        if (target.value > target.node_actions[i].result.value) {
//                            System.out.print("[" + target.value + "->" + target.node_actions[i].result.value + "," + i + "]");
                            target.value = target.node_actions[i].result.value;
                            target.beta = target.value;
                            index = (short) i;
                        }
                        break;
                    }
                    case 1: {
                        double max_res;
                        if (target.node_actions[i].result.calculated) {
                            max_res = target.node_actions[i].result.value;
                            System.err.println("tree::::cut");
                        } else {
                            max_res = find_max(target.node_actions[i].result);
                            if (tree_depth - target.node_actions[i].result.depth <= MAX_TREE_HEU_DEPTH && !tree_memo[cal_loc(0)][cal_loc(1)][cur_ply(target.node_actions[i].result)][1][tree_depth - target.node_actions[i].result.depth - 1].containsKey(req_gen())) {
                                tree_memo[cal_loc(0)][cal_loc(1)][cur_ply(target.node_actions[i].result)][1][tree_depth - target.node_actions[i].result.depth - 1].put(req_gen(), max_res);
                            }
                        }

                        if (target.value > max_res) {
                            target.value = (byte) max_res;
                            target.beta = target.value;
                            index = (short) i;
                        }
                        break;
                    }
                    case -1: {
                        double min_res;
                        if (target.node_actions[i].result.calculated) {
                            min_res = target.node_actions[i].result.value;
                            System.err.println("tree::::cut");
                        } else {
                            min_res = find_min(target.node_actions[i].result);
                            if (tree_depth - target.node_actions[i].result.depth <= MAX_TREE_HEU_DEPTH && !tree_memo[cal_loc(0)][cal_loc(1)][cur_ply(target.node_actions[i].result)][0][tree_depth - target.node_actions[i].result.depth - 1].containsKey(req_gen())) {
                                tree_memo[cal_loc(0)][cal_loc(1)][cur_ply(target.node_actions[i].result)][0][tree_depth - target.node_actions[i].result.depth - 1].put(req_gen(), min_res);
                            }
                        }
                        if (target.value > min_res) {
                            target.value = (byte) min_res;
                            target.beta = target.value;
                            index = (short) i;
                        }
                        break;
                    }

                }

                //TODO active this later
//TODO                if (target.alpha >= target.beta) {
//TODO                    System.out.print("pruned!");
//TODO                    break;
//TODO                }

                if (data[0] == 0) {
                    change_map(false, data[0], p_r, p_c, data[3], target);
                } else {
                    change_map(false, data[0], data[1], data[2], data[3], target);
                }

            }

            if (target.depth == 0) {
                return index;
            }
            return target.value;

        }
    }
    class Node {
        //0 for value
        //1 for max
        //-1 for min
        byte node_type;
        byte depth;
        double value = 0;
        double alpha;
        double beta;
        boolean cut = false;
        boolean calculated = false;
        Transition[] node_actions;
    }
    class Transition {
        byte[] data;
        Node result;

        Transition(byte[] data, Node result) {
            this.data = data;
            this.result = result;
        }
    }
}
