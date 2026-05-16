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
        Schema::create('master_scheduler_config', function (Blueprint $table) {
            $table->id();
            $table->string('scheduler_name'); 
            $table->string('template_name'); 
            $table->string('frequency');
            $table->integer('every')->nullable();
            $table->string('period')->nullable();
            $table->date('starts_on');
            $table->string('expire_on');
            $table->date('ends_on')->nullable(); 
            $table->string('user_type'); 
            $table->string('based_on'); 
            $table->integer('roles')->nullable();
            $table->string('email');

        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('master_scheduler_config', function (Blueprint $table) {
            Schema::dropIfExists('master_scheduler_config');
        });
    }
};
