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
        if (!Schema::hasTable('videos_blogs_master')) {

            Schema::create('videos_blogs_master', function (Blueprint $table) {
                $table->id('id');
                $table->integer('user_type')->nullable();
                $table->enum('content_type',['video','blog'])->nullable();
                $table->string('title')->nullable(); 
                $table->string('description')->nullable();
                $table->string('image')->nullable();
                $table->string('video')->nullable(); 
                $table->string('link')->nullable();
                $table->enum('status', ['N', 'Y'])->nullable();
                $table->integer('role_id')->nullable();
            });
        }
    }
    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('videos_blogs_master');
    }
};
