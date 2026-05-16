<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up(): void
    {
        //
        Schema::create('delegate_master', function (Blueprint $table) {
            $table->id();
            $table->integer('user_id')->comment('user which allow other user to login into his account as delegate');
            $table->integer('delegate_user_id')->comment('user who login as delegate');
            $table->enum('is_active',['Y','N'])->default('N');
            $table->timestamps();

        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        //
        Schema::dropIfExists('delegate_master');
    }
};
