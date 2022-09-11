
public class MainClass {

    public static void main(String[] args) throws InterruptedException {



        main_frame game_frame = new main_frame();


        game_panel game_panel1 = new game_panel(2, game_frame);


        game_frame.setLayout(null);


        game_panel1.setBounds(game_frame.getWidth() / 10, game_frame.getHeight() / 10, game_frame.getWidth() * 8 / 10, game_frame.getHeight() * 8 / 10);

        game_frame.add(game_panel1);


        game_frame.setVisible(true);

    }
}
