defmodule Main do
  def main do
    me = self()

    try do
      try do
        raise :boom
      after
        send(me, :after_ran)
      end
    rescue
      :boom -> recv()
    end
  end
end
