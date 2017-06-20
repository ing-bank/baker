package com.ing.baker;

public class JBakerResponseTest {

//    @Test
//    public void onReceiveCompletedShouldReturnResult() throws ExecutionException, InterruptedException {
//        final Map<String, Object> expectedResult = emptyMap();
//        CompletableFuture<Map<String, Object>> future = CompletableFuture.supplyAsync(() -> {
//            delay();
//            return expectedResult;
//        });
//
//        JBakerResponse response =
//                new JBakerResponse(future, null).onReceiveCompleted((bakerResult, error) -> {
//                    assertTrue(error == null);
//                    assertTrue(bakerResult == expectedResult);
//                });
//        CompletableFuture.allOf(response.receiveAcknowledgement()).join();
//    }
//
//    @Test(expected = RuntimeException.class)
//    public void onReceiveCompletedShouldReturnException() throws Exception {
//        CompletableFuture<Map<String, Object>> future = CompletableFuture.supplyAsync(() -> {
//            delay();
//            throw new RuntimeException("Verifying Exception Handling");
//        });
//
//        JBakerResponse response = new JBakerResponse(future, null).onReceiveCompleted((bakerResult, error) -> {
//            assertTrue(bakerResult == null);
//        });
//
//        CompletableFuture.allOf(response.receiveAcknowledgement()).join();
//    }

    private static void delay() {
        int delay = 500;
        try {
            Thread.sleep(delay);
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
    }
}
