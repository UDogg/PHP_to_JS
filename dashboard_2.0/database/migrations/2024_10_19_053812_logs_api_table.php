<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up()
{
    Schema::create('logs_api_table', function (Blueprint $table) {
        $table->id();
        $table->string('url');
        $table->string('method')->nullable();
        $table->json('headers')->nullable();
        $table->json('request')->nullable();
        $table->text('response')->nullable();
        $table->integer('status_code')->nullable();
        $table->timestamps();
    });
}


    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('logs_api_table');

    }
};
