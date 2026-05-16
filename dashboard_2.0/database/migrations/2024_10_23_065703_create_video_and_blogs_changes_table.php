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
        Schema::create('video_and_blogs_changes', function (Blueprint $table) {
            $table->id();
            $table->integer('user_type');
            $table->enum('content_type',['video','blog']);
            $table->string('title');
            $table->string('description');
            $table->string('image')->nullable();
            $table->string('link'); 
            $table->enum('status', ['N', 'Y']);  
            $table->integer('role_id');
            $table->timestamps();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('video_and_blogs_changes');
    }
};
