defmodule DesktopNativeTest do
  use ExUnit.Case
  doctest DesktopNative

  test "greets the world" do
    assert DesktopNative.hello() == :world
  end
end
